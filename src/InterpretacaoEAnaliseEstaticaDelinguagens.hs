module InterpretacaoEAnaliseEstaticaDelinguagens where

-- ==========================
-- Linguagem funcional simples
-- ==========================

type Id = String
type Numero = Double

data TermoLinFun
  = Identifier Id
  | Literal Numero
  | Lambda Id TermoLinFun
  | Aplicacao TermoLinFun TermoLinFun

data Definicao = Def Id TermoLinFun
type Programa   = [Definicao]

def1 :: Definicao
def1 = Def "inc" (Lambda "x" (Aplicacao (Aplicacao (Identifier "+") (Identifier "x")) (Literal 1)))
def2 = Def "v"   (Aplicacao (Aplicacao (Identifier "+") (Literal 3)) (Literal 2))
def3 = Def "resultado" (Aplicacao (Identifier "inc") (Identifier "v"))
prog1 = [def1,def2,def3]

data ValorFun
  = Numero Double
  | Funcao (ValorFun -> ValorFun)
  | Excecao

instance Show ValorFun where
  show (Numero n) = show n
  show (Funcao _) = "Function definition cannot be printed!"
  show Excecao    = "Excecao durante a execucao do interpretador"

type AmbienteFun = [(Id,ValorFun)]
ambientesimples  = [("+",Funcao (\x -> (Funcao (\y -> somaValorFun x y))))]

somaValorFun (Numero x) (Numero y) = Numero (x+y)
somaValorFun _ _ = Excecao

intTermo a (Identifier i)        = getValor i a
intTermo _ (Literal l)           = Numero l
intTermo a (Lambda i t)          = Funcao (\v -> intTermo ((i,v):a) t)
intTermo a (Aplicacao t1 t2)     = aplica v1 v2
  where v1 = intTermo a t1
        v2 = intTermo a t2

intPrograma _ []                 = Excecao
intPrograma a [(Def _ t)]        = intTermo a t
intPrograma a ((Def i t):ds)     = intPrograma ((i,v):a) ds
  where v = intTermo a t

getValor _ [] = Excecao
getValor i ((j,v):l) = if i == j then v else getValor i l

aplica (Funcao f) v = f v
aplica _ _ = Excecao


-- ==========================
-- Linguagem com estado + OO
-- ==========================

data Termo
  = Var Id
  | Lit Numero
  | Som Termo Termo
  | Lam Id Termo
  | Apl Termo Termo
  | Atr Id Termo
  | Seq Termo Termo
  | For Termo Termo Termo Termo           -- inicio, condicao, final, corpo
  | NewClasse Id [(Id, Termo)] [(Id, Termo)] -- legado/manual (opcional)
  | While Termo Termo
  | GetAttr Termo Id
  | SetAttr Termo Id Termo
  | CallMethod Termo Id Termo
  | DefFunc Id Id Termo
  -- ==== NOVOS ====
  | DefClasse Id (Maybe Id) [(Id, Termo)] [(Id, Id, Termo)] -- nome, pai, attrs default, métodos (nome, param, corpo)
  | New Id [(Id, Termo)]  
  | If Termo Termo Termo
  | InstanceOf Termo Id                                   -- instância por nome da classe + overrides de atributos
  deriving (Eq, Show)

-- Exemplos antigos
termo1 = (Apl (Lam "x" (Som (Var "x") (Lit 2))) (Lit 3))
termo2 = (Apl (Lam "x" (Som (Var "x") (Var "y"))) (Lit 3))
termo3 = (Seq (Atr "y" termo2) termo2)
sq1    = (Seq (Atr "y" (Lit 3)) termo2)
sq2    = (Seq (Atr "y" (Lit 3)) termo3)
sq3    = (Seq (Atr "y" (Som (Atr "z" (Lit 5)) (Var "z"))) termo3)

data Valor
  = Num Double
  | Fun (Valor -> Estado -> (Valor,Estado))
  | Objeto [(Id, Valor)] [(Id, Valor)]            -- atributos, métodos (métodos são Fun)
  | Classe (Maybe Id) [(Id, Valor)] [(Id, Valor)] -- pai, attrs default, métodos (métodos são Fun esperando `self` primeiro)
  | Erro

type Ambiente = [(Id,Valor)]
type Estado   = [(Id,Valor)]

instance Show Valor where
  show (Num x)              = show x
  show Erro                 = "Erro"
  show (Fun _)              = "Função"
  show (Objeto attrs mets)     = "Objeto " ++ show attrs ++ show (map fst mets)
  show (Classe pai attrs mets) = "Classe " ++ show attrs ++ " Métodos: " ++ show (map fst mets) ++ " (pai=" ++ show pai ++ ")"

-- ==========================
-- Interpretador
-- ==========================

-- Busca primeiro no ambiente (a), depois no estado (e)
int :: Ambiente -> Termo -> Estado -> (Valor, Estado)

int a (Var x) e = (search x (a ++ e), e)

int _ (Lit n) e = (Num n, e)

int a (Som t u) e = (somaVal v1 v2, e2)
  where (v1,e1) = int a t e
        (v2,e2) = int a u e1

int a (Lam x t) e = (Fun (\v -> int ((x,v):a) t), e)

int a (Apl t u) e = app v1 v2 e2
  where (v1,e1) = int a t e
        (v2,e2) = int a u e1

int a (Atr x t) e = (v1, wr (x,v1) e1)
  where (v1,e1) = int a t e

int a (Seq t u) e = int a u e1
  where (_,e1) = int a t e

int a (If condT thenT elseT) e =
  case int a condT e of
    (Num v, e1) | v /= 0 -> int a thenT e1
    (Num 0, e1)          -> int a elseT e1
    _                    -> (Erro, e)

int a (InstanceOf objT nomeClasse) e =
  case int a objT e of
    (Objeto attrs _, e1) ->
      case lookup "__className" attrs of
        Just (Classe _ _ _) -> -- não vai acontecer, classe não fica em attr, então usamos tag de classe
          (Num 0, e1)
        _ ->
          case lookup "__class" attrs of
            -- O "__class" poderia guardar o nome como Num ou String (adaptar)
            Just (Num _) -> -- não temos suporte a string nativo, mas podemos usar tag especial
              if isInstance nomeClasse (Objeto attrs []) (a ++ e1)
                then (Num 1, e1)
                else (Num 0, e1)
            _ -> (Num 0, e1)
    _ -> (Num 0, e)

int a (For initT condT finalT corpoT) e =
  let (_, e1) = int a initT e
  in loop e1
  where
    loop estado =
      case int a condT estado of
        (Num v, eCond) | v /= 0 ->
          let (_, eBody)  = int a corpoT eCond
              (_, eFinal) = int a finalT eBody
          in loop eFinal
        (Num 0, eCond)   -> (Num 0, eCond)
        _                -> (Erro, estado)

-- while
int a (While cond corpo) e =
  case int a cond e of
    (Num v, e1) | v /= 0 ->
      let (_, e2) = int a corpo e1
      in int a (While cond corpo) e2
    (Num 0, e1) -> (Num 0, e1)
    _           -> (Erro, e)

-- get
int a (GetAttr obj nomeAttr) e =
  case int a obj e of
    (Objeto attrs _, e') ->
      case lookup nomeAttr attrs of
        Just v  -> (v, e')
        Nothing -> (Erro, e')
    _ -> (Erro, e)

-- set (atualiza no estado se a var existe lá; senão, atualiza o objeto "em memória")
int a (SetAttr (Var nomeVar) nomeAttr termoValor) e =
  case (lookup nomeVar e, search nomeVar (a ++ e)) of
    -- Caso 1: a variável está no estado -> persiste no estado
    (Just (Objeto attrs mets), _) ->
      let (novoValor, e1) = int a termoValor e
          novosAtributos  = (nomeAttr, novoValor)
                          : filter ((/= nomeAttr) . fst) attrs
          novoObjeto      = Objeto novosAtributos mets
          e2              = (nomeVar, novoObjeto)
                          : filter ((/= nomeVar) . fst) e1
      in (novoObjeto, e2)

    -- Caso 2: não está no estado, mas resolve para Objeto no ambiente (ex.: "this")
    (Nothing, Objeto attrs mets) ->
      let (novoValor, e1) = int a termoValor e
          novosAtributos  = (nomeAttr, novoValor)
                          : filter ((/= nomeAttr) . fst) attrs
          novoObjeto      = Objeto novosAtributos mets
      in (novoObjeto, e1)

    -- Demais casos: erro
    _ -> (Erro, e)

-- chamada de método: obj.metodo(arg)
int a (CallMethod obj nomeMetodo arg) e =
  case int a obj e of
    (Objeto attrs mets, e1) ->
      case lookup nomeMetodo mets of
        Just (Fun fSelf) ->
          -- aplica `self` primeiro
          let (vFunArg, eSelf) = fSelf (Objeto attrs mets) e1
          in case vFunArg of
               Fun fArg ->
                 let (valArg, e2) = int a arg eSelf
                 in fArg valArg e2
               _ -> (Erro, eSelf)
        _ -> (Erro, e1)
    _ -> (Erro, e)

-- define função solta e salva no estado
int a (DefFunc nome param corpo) e =
  let func = Fun (\v est -> int ((param, v) : (a ++ e)) corpo est)
      e'   = wr (nome, func) e
  in (func, e')

-- =========
-- OO legado (opcional): NewClasse "manual" sem herança
-- =========
--int a (NewClasse _ attrs mets) e =
 -- let (valAttrs, eFinal) =
 --       foldl
 --         (\(acc, est) (nome, termo) ->
 --             let (v, est') = int a termo est
 --             in (acc ++ [(nome, v)], est'))
 --         ([], e) attrs
 --     (valMets, eFinal2) =
 --       foldl
 --         (\(acc, est) (nome, termo) ->
 --             let (v, est') = int a termo est
 --             in (acc ++ [(nome, v)], est'))
 --         ([], eFinal) mets
 -- in (Objeto valAttrs valMets, eFinal2)

-- =========
-- NOVO: classes e herança (AS CLÁUSULAS DE `int` DEVEM VIR AQUI!)
-- =========

-- definição de classe no estado
int a (DefClasse nome maybePai attrsT metsT) e =
  let -- avalia atributos default
      (attrsV, e1) =
        foldl
          (\(acc, est) (k, t) ->
              let (v, est') = int a t est
              in (acc ++ [(k, v)], est'))
          ([], e) attrsT

      -- compila métodos (nome, param, corpo) -> (nome, Fun que espera `self`)
      metsV =
        [ (mNome, buildMethod a mParam mCorpo)
        | (mNome, mParam, mCorpo) <- metsT
        ]

      classe = Classe maybePai attrsV metsV
      e2     = wr (nome, classe) e1
  in (classe, e2)

-- instanciação por nome de classe (com herança)
int a (New nomeClasse initsT) e =
  case resolveClassChain a e nomeClasse of
    Nothing -> (Erro, e)
    Just chain ->
      let (baseAttrs, baseMets) = collectClassAM chain
          (initAttrs, e1) =
            foldl
              (\(acc, est) (k, t) ->
                  let (v, est') = int a t est
                  in (acc ++ [(k, v)], est'))
              ([], e)
              initsT
          classVal = last chain  -- pega a classe mais derivada
          finalAttrs = mergeKV (("__class", classVal) : initAttrs) baseAttrs
          finalMets  = baseMets
      in (Objeto finalAttrs finalMets, e1)

-- =========
-- NOVO: classes e herança
-- =========

-- Função para checar herança
isInstance :: Id -> Valor -> Ambiente -> Bool
isInstance nomeClasse (Objeto attrs _) env =
  case lookup "__class" attrs of
    Just (Classe maybePai _ _) ->
      case search nomeClasse env of
        Classe _ _ _ -> True
        _ -> case maybePai of
              Just paiNome -> nomeClasse == paiNome
              Nothing      -> False
    _ -> False
isInstance _ _ _ = False

-- mescla por chave (filho sobrescreve pai)
mergeKV :: [(Id, Valor)] -> [(Id, Valor)] -> [(Id, Valor)]
mergeKV filho pai =
  let keys = map fst filho
  in filho ++ filter (\(k,_) -> k `notElem` keys) pai

-- resolve cadeia de herança (do topo até a classe pedida)
resolveClassChain :: Ambiente -> Estado -> Id -> Maybe [Valor]
resolveClassChain a e nome = go nome []
  where
    go n acc = case search n (a ++ e) of
      Classe maybePai attrs mets ->
        case maybePai of
          Nothing     -> Just (reverse (Classe maybePai attrs mets : acc))
          Just paiNom -> go paiNom (Classe maybePai attrs mets : acc)
      _ -> Nothing

-- coleta attrs/métodos acumulados (pai -> ... -> filho)
collectClassAM :: [Valor] -> ([(Id,Valor)], [(Id,Valor)])
collectClassAM vs =
  foldl
    (\(accA, accM) v -> case v of
        Classe _ a m -> (mergeKV a accA, mergeKV m accM)
        _            -> (accA, accM))
    ([],[])
    vs

-- constrói método que captura `this` e depois o argumento
buildMethod :: Ambiente -> Id -> Termo -> Valor
buildMethod a param corpo =
  -- Fun que espera `self`; ao aplicar, devolve Fun que espera `arg`
  Fun (\self est1 ->
        ( Fun (\arg est2 ->
                int (("this", self):(param, arg):a) corpo est2
              )
        , est1))

-- =========
-- Primitivas de apoio
-- =========

search :: Eq a => a -> [(a, Valor)] -> Valor
search _ [] = Erro
search i ((j,v):l) = if i == j then v else search i l

somaVal :: Valor -> Valor -> Valor
somaVal (Num x) (Num y) = Num (x+y)
somaVal _ _ = Erro

app :: Valor -> Valor -> Estado -> (Valor, Estado)
app (Fun f) v e = f v e
app _ _ e       = (Erro, e)

wr :: Eq a => (a, t) -> [(a, t)] -> [(a, t)]
wr (i,v) []         = [(i,v)]
wr (i,v) ((j,u):l)  = if (i == j) then (j,v):l else (j,u) : wr (i,v) l

-- atalho
at :: Termo -> (Valor, Estado)
at t = int [] t []

-- ==========================
-- Testes
-- ==========================

-- while original
testeWhile :: Termo
testeWhile =
  Seq
    (Atr "x" (Lit 0))
    (Seq
      (While (Som (Lit 1) (Som (Var "x") (Lit (-5))))
        (Atr "x" (Som (Var "x") (Lit 1)))
      )
      (Var "x")
    )

-- Classe sem herança
defClasseQuadrado :: Termo
defClasseQuadrado =
  DefClasse "Quadrado" Nothing
    [("lado", Lit 0)]  -- atributo lado, default 0
    [ ("perimetro", "self",
        -- O perímetro é a soma dos 4 lados
        Som (Som (GetAttr (Var "self") "lado") (GetAttr (Var "self") "lado"))
            (Som (GetAttr (Var "self") "lado") (GetAttr (Var "self") "lado"))
      )
    ]
novoQuadrado :: Termo
novoQuadrado = New "Quadrado" [("lado", Lit 5)]

testeQuadrado :: Termo
testeQuadrado =
  Seq
    defClasseQuadrado
    (Seq
      (Atr "q" novoQuadrado)
      (CallMethod (Var "q") "perimetro" (Var "q")) -- chama q.perimetro()
    )

-- Teste para SetAttr
testeSet :: Termo
testeSet =
  Seq
    defClasseQuadrado
    (Seq
      (Atr "q" novoQuadrado) -- Cria um objeto 'q' com lado 5
      (SetAttr (Var "q") "lado" (Lit 10)) -- Altera o lado para 10. O resultado do SetAttr é o objeto atualizado.
    )

-- Teste para GetAttr
testeGet :: Termo
testeGet =
  Seq
    defClasseQuadrado
    (Seq
      (Atr "q" novoQuadrado) -- Cria um objeto 'q' com lado 5
      (GetAttr (Var "q") "lado") -- Lê o valor do lado. O resultado é o valor em si.
    )

-- Definições de classe e herança
-- class Ponto { x=0, y=0; move(dx) { this.x := this.x + dx } }
defClassePonto :: Termo
defClassePonto =
  DefClasse "Ponto" Nothing
    [("x", Lit 0), ("y", Lit 0)]
    [ ("move", "dx",
        SetAttr (Var "this") "x" (Som (GetAttr (Var "this") "x") (Var "dx"))
      )
    ]

-- class Ponto3D extends Ponto { z=0; moveZ(dz) { this.z := this.z + dz } }
defClassePonto3D :: Termo
defClassePonto3D =
  DefClasse "Ponto3D" (Just "Ponto")
    [("z", Lit 0)]
    [ ("moveZ", "dz",
        SetAttr (Var "this") "z" (Som (GetAttr (Var "this") "z") (Var "dz"))
      )
    ]

-- new Ponto3D { x=10, y=20 }
mkP :: Termo
mkP = New "Ponto3D" [("x", Lit 10), ("y", Lit 20)]

-- p := new Ponto3D(...);
-- p := p.move(5);
-- p := p.moveZ(7);
-- lê z (deve dar 7)
testeClasseHeranca :: Termo
testeClasseHeranca =
  Seq
    defClassePonto
    (Seq
      defClassePonto3D
      (Seq
        (Atr "p" mkP)
        (Seq
          (Atr "p" (CallMethod (Var "p") "move"  (Lit 5)))
          (Seq
            (Atr "p" (CallMethod (Var "p") "moveZ" (Lit 7)))
            (GetAttr (Var "p") "z")
          )
        )
      )
    )

-- Runner
testOO :: Termo -> IO ()
testOO t =
  let (resultado, novoEstado) = int [] t []
  in do
    putStrLn $ "Resultado: "   ++ show resultado
    putStrLn $ "Novo estado: " ++ show novoEstado



-- ==========================
-- main
-- ==========================

main :: IO ()
main = do

    putStrLn "\nTeste do while:"
    testOO testeWhile

    putStrLn "\nTeste do get:"
    testOO testeGet

    putStrLn "\nTeste do set:"
    testOO testeSet

    putStrLn "\nTeste de classe sem herança:"
    testOO testeQuadrado

    putStrLn "\nTeste de classe + herança:"
    testOO testeClasseHeranca
