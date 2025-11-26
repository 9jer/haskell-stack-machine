module Main where

import Text.Read (readMaybe)
import Control.Monad (foldM)
import Data.List (intercalate)

data Tree a = Empty 
            | Node (Tree a) a (Tree a) 
            deriving (Show, Eq)

instance Functor Tree where
    fmap _ Empty = Empty
    fmap f (Node l x r) = Node (fmap f l) (f x) (fmap f r)

treeSize :: Tree a -> Int
treeSize Empty = 0
treeSize (Node l _ r) = 1 + treeSize l + treeSize r

flattenDFS :: Tree a -> [a]
flattenDFS Empty = []
flattenDFS (Node l x r) = flattenDFS l ++ [x] ++ flattenDFS r

treeTraverseD :: (a -> b -> b) -> b -> Tree a -> b
treeTraverseD f acc tree = foldr f acc (flattenDFS tree)

flattenBFS :: Tree a -> [a]
flattenBFS t = traverse [t]
  where
    traverse [] = []
    traverse (Empty:xs) = traverse xs
    traverse (Node l x r : xs) = x : traverse (xs ++ [l, r])

treeTraverseW :: (a -> b -> b) -> b -> Tree a -> b
treeTraverseW f acc tree = foldr f acc (flattenBFS tree)

data Expr = Const Double
          | Var String
          | Add Expr Expr
          | Sub Expr Expr
          | Mul Expr Expr
          | Div Expr Expr
          deriving (Show, Eq)

toTree :: Expr -> Tree String
toTree (Const c) = Node Empty (show c) Empty
toTree (Var v)   = Node Empty v Empty
toTree (Add l r) = Node (toTree l) "+" (toTree r)
toTree (Sub l r) = Node (toTree l) "-" (toTree r)
toTree (Mul l r) = Node (toTree l) "*" (toTree r)
toTree (Div l r) = Node (toTree l) "/" (toTree r)

type Context = [(String, Double)]

evalExpr :: Context -> Expr -> Either String Double
evalExpr _ (Const c) = Right c
evalExpr ctx (Var v) = case lookup v ctx of
                         Just val -> Right val
                         Nothing  -> Left $ "Variable not found: " ++ v
evalExpr ctx (Add l r) = (+) <$> evalExpr ctx l <*> evalExpr ctx r
evalExpr ctx (Sub l r) = (-) <$> evalExpr ctx l <*> evalExpr ctx r
evalExpr ctx (Mul l r) = (*) <$> evalExpr ctx l <*> evalExpr ctx r
evalExpr ctx (Div l r) = do
    nr <- evalExpr ctx r
    if nr == 0 then Left "Division by zero in expression"
    else (/) <$> evalExpr ctx l <*> pure nr

simplify :: Expr -> Expr
simplify (Add e1 e2) = 
    let (s1, s2) = (simplify e1, simplify e2)
    in case (s1, s2) of
        (Const 0, r) -> r
        (l, Const 0) -> l
        (Const a, Const b) -> Const (a + b)
        _ -> Add s1 s2
simplify (Mul e1 e2) =
    let (s1, s2) = (simplify e1, simplify e2)
    in case (s1, s2) of
        (Const 0, _) -> Const 0
        (_, Const 0) -> Const 0
        (Const 1, r) -> r
        (l, Const 1) -> l
        (Const a, Const b) -> Const (a * b)
        _ -> Mul s1 s2
simplify (Sub e1 e2) = 
    let (s1, s2) = (simplify e1, simplify e2)
    in if s1 == s2 then Const 0 else Sub s1 s2
simplify x = x

diff :: String -> Expr -> Expr
diff _ (Const _) = Const 0
diff var (Var v) 
    | var == v  = Const 1
    | otherwise = Const 0
diff var (Add l r) = Add (diff var l) (diff var r)
diff var (Sub l r) = Sub (diff var l) (diff var r)
diff var (Mul l r) = Add (Mul (diff var l) r) (Mul l (diff var r))
diff var (Div u v) = Div (Sub (Mul (diff var u) v) (Mul u (diff var v))) (Mul v v)

data Instruction = IPush Double
                 | IFetch String
                 | IAdd | ISub | IMul | IDiv
                 | IPrint 
                 deriving (Show, Read, Eq)

type Stack = [Double]
type Program = [Instruction]

runProgram :: Program -> Context -> Either String Stack
runProgram prog ctx = foldM (step ctx) [] prog

step :: Context -> Stack -> Instruction -> Either String Stack
step _ s (IPush val) = Right (val : s)
step ctx s (IFetch name) = 
    case lookup name ctx of
        Just val -> Right (val : s)
        Nothing  -> Left $ "Unknown variable: " ++ name
step _ (x:y:rest) IAdd = Right ((y + x) : rest)
step _ (x:y:rest) ISub = Right ((y - x) : rest)
step _ (x:y:rest) IMul = Right ((y * x) : rest)
step _ (x:y:rest) IDiv = 
    if x == 0 then Left "Division by zero" 
    else Right ((y / x) : rest)
step _ _ op | op `elem` [IAdd, ISub, IMul, IDiv] = Left "Not enough operands on stack"
step _ s IPrint = Right s

parseProgram :: String -> Either String Program
parseProgram str = mapM parseLine (lines str)
  where
    parseLine :: String -> Either String Instruction
    parseLine l = case words l of
        ["push", x] -> case readMaybe x of
                         Just n  -> Right (IPush n)
                         Nothing -> Right (IFetch x)
        ["add"]     -> Right IAdd
        ["sub"]     -> Right ISub
        ["mul"]     -> Right IMul
        ["div"]     -> Right IDiv
        ["print"]   -> Right IPrint
        cmd         -> Left $ "Unknown command: " ++ unwords cmd

compileExpr :: Expr -> Program
compileExpr (Const c) = [IPush c]
compileExpr (Var v)   = [IFetch v]
compileExpr (Add l r) = compileExpr l ++ compileExpr r ++ [IAdd]
compileExpr (Sub l r) = compileExpr l ++ compileExpr r ++ [ISub]
compileExpr (Mul l r) = compileExpr l ++ compileExpr r ++ [IMul]
compileExpr (Div l r) = compileExpr l ++ compileExpr r ++ [IDiv]

main :: IO ()
main = do
    putStrLn "--- 1. Tree DFS/BFS Tests ---"
    let myTree = Node (Node (Node Empty 4 Empty) 2 (Node Empty 5 Empty)) 1 (Node (Node Empty 6 Empty) 3 (Node Empty 7 Empty))
    
    putStrLn "DFS:"
    print $ treeTraverseD (:) [] myTree
    
    putStrLn "BFS:"
    print $ treeTraverseW (:) [] myTree

    putStrLn "\n--- 2. Expression & Stack Machine ---"
    let expr = Add (Add (Mul (Const 2) (Mul (Var "x") (Var "x"))) (Mul (Const 4) (Var "x"))) (Const 5)
    let ctx = [("x", 3.0)]

    putStrLn $ "Expression: " ++ show expr
    putStrLn "Evaluating Expr directly:"
    print $ evalExpr ctx expr

    putStrLn "Compiling Expr to Stack Code:"
    let code = compileExpr expr
    mapM_ print code

    putStrLn "Running Compiled Code (Stack VM):"
    case runProgram code ctx of
        Left err -> putStrLn $ "Error: " ++ err
        Right stack -> putStrLn $ "Result stack: " ++ show stack

    putStrLn "\n--- 3. Error Handling Test ---"
    let badCode = [IPush 10, IPush 0, IDiv]
    print $ runProgram badCode []

    putStrLn "\n--- 4. Simplification & Differentiation ---"
    let expr2 = Add (Mul (Const 1) (Var "x")) (Const 0)
    putStrLn $ "Original: " ++ show expr2
    putStrLn $ "Simplified: " ++ show (simplify expr2)
    
    let expr3 = Mul (Var "x") (Var "x")
    putStrLn $ "Diff (x^2) by x: " ++ show (simplify (diff "x" expr3))