-- Differential-test driver around Isabelle's own Haskell export of WEST
-- (AFP WEST_Algorithms.thy: `export_code simp_pad_WEST_reg`). Reads prefix
-- formulas (see gen.py) from stdin; prints, per formula, `WEST_reg` and
-- `simp_pad_WEST_reg` in the format of `show` on Isabelle lists.
import WEST_simp_pad
import Data.List (intercalate)

nat :: Integer -> Nat
nat 0 = Zero_nat
nat k = Suc (nat (k - 1))

tok :: String -> [String]
tok = words . concatMap (\c -> if c == '(' || c == ')' then [' ', c, ' '] else [c])

parse :: [String] -> (Mltl Nat, [String])
parse ("T" : r) = (True_mltl, r)
parse ("F" : r) = (False_mltl, r)
parse ("(" : op : r) = let (f, rest) = go op r in case rest of (")" : r') -> (f, r'); _ -> error "missing )"
  where
    num (x : r') = (nat (read x), r')
    go "P" r0 = let (n, r1) = num r0 in (Prop_mltl n, r1)
    go "N" r0 = let (x, r1) = parse r0 in (Not_mltl x, r1)
    go "A" r0 = let (x, r1) = parse r0; (y, r2) = parse r1 in (And_mltl x y, r2)
    go "O" r0 = let (x, r1) = parse r0; (y, r2) = parse r1 in (Or_mltl x y, r2)
    go "Fu" r0 = let (a, r1) = num r0; (b, r2) = num r1; (x, r3) = parse r2 in (Future_mltl a b x, r3)
    go "G" r0 = let (a, r1) = num r0; (b, r2) = num r1; (x, r3) = parse r2 in (Global_mltl a b x, r3)
    go "U" r0 = let (x, r1) = parse r0; (a, r2) = num r1; (b, r3) = num r2; (y, r4) = parse r3 in (Until_mltl x a b y, r4)
    go "R" r0 = let (x, r1) = parse r0; (a, r2) = num r1; (b, r3) = num r2; (y, r4) = parse r3 in (Release_mltl x a b y, r4)
    go o _ = error ("bad op " ++ o)
parse t = error ("bad formula " ++ unwords (take 3 t))

bit :: WEST_bit -> String
bit Zero = "Zero"
bit One = "One"
bit S = "S"

list :: [String] -> String
list xs = "[" ++ intercalate "," xs ++ "]"

showRegex :: [[[WEST_bit]]] -> String
showRegex = list . map (list . map (list . map bit))

main :: IO ()
main = do
  input <- getContents
  mapM_ (\l -> let f = fst (parse (tok l)) in do
            putStrLn (showRegex (wEST_reg f))
            putStrLn (showRegex (simp_pad_WEST_reg f)))
        (filter (not . null) (lines input))
