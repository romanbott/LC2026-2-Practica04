module Practica04 where

-- Sintaxis de la logica proposicional
data Prop
  = Var String
  | Cons Bool
  | Not Prop
  | And Prop Prop
  | Or Prop Prop
  | Impl Prop Prop
  | Syss Prop Prop
  deriving (Eq)

instance Show Prop where
  show (Cons True) = "⊤"
  show (Cons False) = "⊥"
  show (Var p) = p
  show (Not p) = "¬" ++ show p
  show (Or p q) = "(" ++ show p ++ " ∨ " ++ show q ++ ")"
  show (And p q) = "(" ++ show p ++ " ∧ " ++ show q ++ ")"
  show (Impl p q) = "(" ++ show p ++ " → " ++ show q ++ ")"
  show (Syss p q) = "(" ++ show p ++ " ↔ " ++ show q ++ ")"

type Literal = Prop

type Clausula = [Literal]

p, q, r, s, t, u :: Prop
p = Var "p"
q = Var "q"
r = Var "r"
s = Var "s"
t = Var "t"
u = Var "u"

-- Definicion de los tipos para la practica
type Interpretacion = [(String, Bool)]

type Estado = (Interpretacion, [Clausula])

-- IMPLEMENTACION PARTE 1
-- Ejercicio 1
conflict :: Estado -> Bool
conflict (_, cs) = [] `elem` cs

-- Ejercicio 2
success :: Estado -> Bool
success (_, cs) = null cs

-- Función auxiliar para convertir una literal a una asignación de verdad.
literalToInterp :: Literal -> (String, Bool)
literalToInterp c = case c of
  Not (Var v) -> (v, False)
  Var v -> (v, True)

-- Función auxiliar para convertir una asignación de verdad a una literal.
interpToLiteral :: (String, Bool) -> Literal
interpToLiteral (v, True) = Var v
interpToLiteral (v, False) = Not (Var v)

-- Ejercicio 3
unit :: Estado -> Estado
unit (interp, [l] : cs) = (literalToInterp l : interp, cs)
unit (interp, clausula : cs) =
  let (nueva_interp, nuevas_clausulas) = unit (interp, cs)
   in (nueva_interp, clausula : nuevas_clausulas)
unit estado = estado

-- Función que eliminia una literal de una cláusula.
elimLit :: [Clausula] -> (String, Bool) -> [Clausula]
elimLit [] _ = []
elimLit (c : cs) interp =
  if lit `elem` c
    then elimLit cs interp
    else c : elimLit cs interp
  where
    lit = interpToLiteral interp

-- Ejercicio 4
elim :: Estado -> Estado
elim (is, cs) = (is, foldl elimLit cs is)

-- Función que reduce una cláusula mediante una asigación Variable -> valor.
redLit :: Clausula -> (String, Bool) -> Clausula
redLit [] _ = []
redLit c (v, b) = filter (\x -> x /= interpToLiteral (v, not b)) c

-- Ejercicio 5
red :: Estado -> Estado
red (is, cs) = (is, map (\c -> foldl redLit c is) cs)

-- Ejercicio 6
sep :: Literal -> Estado -> (Estado, Estado)
sep lit (interp, cs) = (estadoTrue, estadoFalse)
  where
    nombreVar = case lit of
      Var x -> x
      Not (Var x) -> x

    estadoTrue = ((nombreVar, True) : interp, cs)
    estadoFalse = ((nombreVar, False) : interp, cs)

-- IMPLEMENTACION PARTE 2

-- Función que cuenta las ocurrencias de cada literal en una lista de claúsulas devolviendo el resultado como una lista de (litera, conteo)
cuentaLiterales :: [Clausula] -> [(Literal, Integer)]
cuentaLiterales cs = procesarLista (concat cs) []
  where
    procesarLista [] acumulador = acumulador
    procesarLista (x : xs) acumulador = procesarLista xs (actualizarConteo x acumulador)

    actualizarConteo :: Literal -> [(Literal, Integer)] -> [(Literal, Integer)]
    actualizarConteo l [] = [(l, 1)]
    actualizarConteo l ((var, cant) : resto)
      | l == var = (var, cant + 1) : resto
      | otherwise = (var, cant) : actualizarConteo l resto

-- Función que busca el máximo en una lista de parejas de la forma (literal, valor)
obtenerMaximo :: [(Literal, Integer)] -> (Literal, Integer)
obtenerMaximo [] = error "Lista vacía"
obtenerMaximo [x] = x
obtenerMaximo (x : xs) = mayor x (obtenerMaximo xs)
  where
    mayor (c1, n1) (c2, n2)
      | n1 >= n2 = (c1, n1)
      | otherwise = (c2, n2)

-- Ejercicio 1
-- Busca la literal con más ocurrencias en las clausulas
heuristicsLiteral :: [Clausula] -> Literal
heuristicsLiteral cs =
  let (lit, _) = obtenerMaximo (cuentaLiterales cs)
   in lit

-- Dado un estado, aplica `heuristicsLiteral` a las claúsulas
heuristicaEstado :: Estado -> Literal
heuristicaEstado (_, cs) = heuristicsLiteral cs

data ArbolDPLL = Node Estado ArbolDPLL | Branch Estado ArbolDPLL ArbolDPLL | Void deriving (Show)

-- Aplica `unit` `elim` y `red` hasta que ya no haya cambios en el estado
simplifica :: Estado -> Estado
simplifica estado = if nuevo_estado == estado then estado else simplifica nuevo_estado
  where
    nuevo_estado = (unit . elim . red) estado

-- Función que construye un árbol mediante el
-- algoritmo DPLL empezando en la raíz con el estado dado,
-- aplicando `simplifica` en cada paso, y bifurcando el arbol
-- en cada estado que no sea exitoso ni contradictorio.
construyeArbol :: Estado -> ArbolDPLL
construyeArbol estado
  | success simplificado = Node simplificado Void
  | conflict simplificado = Void
  | otherwise =
      let literalExpandir = heuristicaEstado simplificado
          (left, right) = sep literalExpandir simplificado
       in Branch estado (construyeArbol left) (construyeArbol right)
  where
    simplificado = simplifica estado

-- Función que dado un arbol construido con el algoritmo DPLL
-- busca un Nodea y devuelve el modelo encontrado
-- o devuelve [] si no encuentra lo encuentra.
encontrarModelo :: ArbolDPLL -> Interpretacion
encontrarModelo Void = []
encontrarModelo (Node (interp, _) _) = interp
encontrarModelo (Branch _ izq der) =
  case encontrarModelo izq of
    [] -> encontrarModelo der
    m -> m

-- EJERCICIO 2
dpll :: [Clausula] -> Interpretacion
dpll cs = encontrarModelo (construyeArbol ([], cs))

-- Funcion auxiliar que elimina condicionales y bicondicionales
elimImpl :: Prop -> Prop
elimImpl prop = case prop of
  Impl a b -> Or (Not (elimImpl a)) (elimImpl b)
  Syss a b -> And (Or (Not (elimImpl a)) (elimImpl b)) (Or (Not (elimImpl b)) (elimImpl a))
  Not inner -> Not (elimImpl inner)
  Or a b -> Or (elimImpl a) (elimImpl b)
  And a b -> And (elimImpl a) (elimImpl b)
  x -> x

-- Funcion auxiliar que mete `Not` hacia las hojas del ASA.
meteNeg :: Prop -> Prop
meteNeg prop = case prop of
  Not (Not a) -> meteNeg a
  Not (And a b) -> Or (meteNeg (Not a)) (meteNeg (Not b))
  Not (Or a b) -> And (meteNeg (Not a)) (meteNeg (Not b))
  Or a b -> Or (meteNeg a) (meteNeg b)
  And a b -> And (meteNeg a) (meteNeg b)
  x -> x

fnn :: Prop -> Prop
fnn = meteNeg . elimImpl

-- Funcion auxiliar que usa la distributividad de Or sobre And
-- para meter el Or hacia las hojas del ASA.
meteOr :: Prop -> Prop
meteOr (Or a (And b c)) = And (meteOr (Or a b)) (meteOr (Or a c))
meteOr (Or (And a b) c) = And (meteOr (Or a c)) (meteOr (Or b c))
meteOr x = x

-- Funcion auxiliar que convierte una proposición en FNN a FNC
fnnAFnc :: Prop -> Prop
fnnAFnc (And a b) = And (fnnAFnc a) (fnnAFnc b)
fnnAFnc (Or a b) = meteOr (Or (fnnAFnc a) (fnnAFnc b))
fnnAFnc a = a

fnc :: Prop -> Prop
fnc = fnnAFnc . fnn

-- Funcion auxiliar que toma una lista
-- como entrada y devuelve una lista sin repeticiones
unique :: (Eq a) => [a] -> [a]
unique [] = []
unique (x : xs)
  | x `elem` xs = xs'
  | otherwise = x : xs'
  where
    xs' = unique xs

-- Funcion auxiliar que toma una lista de `a` una función de `a` en `b`
-- y aplica la función a cada elemento de la lista.
mapea :: (a -> b) -> [a] -> [b]
mapea _ [] = []
mapea f (x : xs) = f x : mapea f xs

-- Función que devuelve las literales de una proposición que es una cláusula.
-- Es decir la proposición debe tener únicamente Or en el cuerpo del ASA, y Not posiblemente en las hojas.
literales :: Prop -> Clausula
literales (Or a b) = literales a ++ literales b
literales x = [x]

-- Función que devuelve las claúsulas de una proposición. Se asume que está en FNC.
clausulas :: Prop -> [Clausula]
clausulas (And a b) = clausulas a ++ clausulas b
clausulas a = [unique (literales a)]

-- EXTRA
dpll2 :: Prop -> Interpretacion
dpll2 = dpll . clausulas . fnc
