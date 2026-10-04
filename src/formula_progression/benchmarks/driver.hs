{-# LANGUAGE StandaloneDeriving, BangPatterns #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
-- Benchmark driver for the Isabelle-exported Haskell `prog`
-- (ROOT/formula_progression_api/codegen/formula_progression.hs, used as is).
--
--   fp_hs <mode> formulas.txt traces.txt min_seconds
--   mode: prog       prog f trace, per (formula, trace) pair
--         prog-step  prog over one state at a time, feeding each result back,
--                    stopping at True/False (what the deployed API does)
--
-- Prints: haskell-<mode>,formulas,traces,reps,total_s,ns_per_call,hash
-- hash = FNV-1a of every result formula (prefix notation, '\n'-terminated),
-- identical to the Rust driver's, so answers can be compared.
import Formula_progression (Nat(..), Set(..), Mltl(..), prog)
import System.Environment (getArgs)
import GHC.Clock (getMonotonicTimeNSec)
import Control.Exception (evaluate)
import Data.Bits (xor)
import Data.Char (ord)
import Data.List (foldl')
import Data.Word (Word64)
import Numeric (showHex)

deriving instance Eq Nat

toNat :: Int -> Nat
toNat 0 = Zero_nat
toNat k = Suc (toNat (k - 1))

fromNat :: Nat -> Int
fromNat = go 0 where
  go !acc Zero_nat = acc
  go !acc (Suc n) = go (acc + 1) n

parseF :: [String] -> (Mltl Nat, [String])
parseF ("true" : r) = (True_mltl, r)
parseF ("false" : r) = (False_mltl, r)
parseF ("!" : r) = let (a, r1) = parseF r in (Not_mltl a, r1)
parseF ("&" : r) = two And_mltl r
parseF ("|" : r) = two Or_mltl r
parseF ("F" : a : b : r) = let (x, r1) = parseF r in (Future_mltl (toNat (read a)) (toNat (read b)) x, r1)
parseF ("G" : a : b : r) = let (x, r1) = parseF r in (Global_mltl (toNat (read a)) (toNat (read b)) x, r1)
parseF ("U" : a : b : r) = let (x, r1) = parseF r; (y, r2) = parseF r1 in (Until_mltl x (toNat (read a)) (toNat (read b)) y, r2)
parseF ("R" : a : b : r) = let (x, r1) = parseF r; (y, r2) = parseF r1 in (Release_mltl x (toNat (read a)) (toNat (read b)) y, r2)
parseF (('p' : ds) : r) = (Prop_mltl (toNat (read ds)), r)
parseF t = error ("bad formula at " ++ unwords (take 5 t))

two :: (Mltl Nat -> Mltl Nat -> Mltl Nat) -> [String] -> (Mltl Nat, [String])
two c r = let (x, r1) = parseF r; (y, r2) = parseF r1 in (c x y, r2)

parseTrace :: String -> [Set Nat]
parseTrace l = [Set [toNat i | (i, c) <- zip [0 ..] s, c == '1'] | s <- words l]

-- Prefix printing (also forces the whole result).
pr :: Mltl Nat -> String
pr True_mltl = "true"
pr False_mltl = "false"
pr (Prop_mltl p) = "p" ++ show (fromNat p)
pr (Not_mltl f) = "! " ++ pr f
pr (And_mltl f g) = "& " ++ pr f ++ " " ++ pr g
pr (Or_mltl f g) = "| " ++ pr f ++ " " ++ pr g
pr (Future_mltl a b f) = "F " ++ show (fromNat a) ++ " " ++ show (fromNat b) ++ " " ++ pr f
pr (Global_mltl a b f) = "G " ++ show (fromNat a) ++ " " ++ show (fromNat b) ++ " " ++ pr f
pr (Until_mltl f a b g) = "U " ++ show (fromNat a) ++ " " ++ show (fromNat b) ++ " " ++ pr f ++ " " ++ pr g
pr (Release_mltl f a b g) = "R " ++ show (fromNat a) ++ " " ++ show (fromNat b) ++ " " ++ pr f ++ " " ++ pr g

-- Strict traversal that forces every constructor and bound (cheap next to prog).
force :: Mltl Nat -> Int
force True_mltl = 1
force False_mltl = 1
force (Prop_mltl p) = 1 + fromNat p
force (Not_mltl f) = 1 + force f
force (And_mltl f g) = 1 + force f + force g
force (Or_mltl f g) = 1 + force f + force g
force (Future_mltl a b f) = 1 + fromNat a + fromNat b + force f
force (Global_mltl a b f) = 1 + fromNat a + fromNat b + force f
force (Until_mltl f a b g) = 1 + fromNat a + fromNat b + force f + force g
force (Release_mltl f a b g) = 1 + fromNat a + fromNat b + force f + force g

terminal :: Mltl a -> Bool
terminal True_mltl = True
terminal False_mltl = True
terminal _ = False

stepwise :: Mltl Nat -> [Set Nat] -> Mltl Nat
stepwise f [] = f
stepwise f (h : t) = let r = prog f [h] in if terminal r then r else stepwise r t

run :: String -> Mltl Nat -> [Set Nat] -> Mltl Nat
run "prog" = prog
run "prog-step" = stepwise
run m = error ("unknown mode " ++ m)

-- One pass over all pairs. NOINLINE + -fno-full-laziness: every pass recomputes.
{-# NOINLINE pass #-}
pass :: String -> Int -> [Mltl Nat] -> [[Set Nat]] -> Int
pass mode i fs ts = i `seq` foldl' (+) 0 [force (run mode f t) | f <- fs, t <- ts]

fnv :: String -> Word64
fnv = foldl' (\h c -> (h `xor` fromIntegral (ord c)) * 1099511628211) 14695981039346656037

main :: IO ()
main = do
  [mode, ff, tf, ms] <- getArgs
  fs <- map (fst . parseF . words) . filter (not . null) . lines <$> readFile ff
  ts <- map parseTrace . filter (not . null) . lines <$> readFile tf
  _ <- evaluate (sum (map force fs) + sum (map (sum . map (\(Set xs) -> length xs)) ts))
  let minNs = round (read ms * 1e9 :: Double) :: Word64
      loop !reps !acc t0 = do
        _ <- evaluate (pass mode reps fs ts)
        t1 <- getMonotonicTimeNSec
        if t1 - t0 >= minNs then return (reps + 1, t1 - t0, acc) else loop (reps + 1) acc t0
  t0 <- getMonotonicTimeNSec
  (reps, total, _) <- loop (0 :: Int) (0 :: Int) t0
  let h = fnv (concat [pr (run mode f t) ++ "\n" | f <- fs, t <- ts])
      calls = fromIntegral (reps * length fs * length ts) :: Double
      secs = fromIntegral total / 1e9 :: Double
  putStrLn ("haskell-" ++ mode ++ "," ++ show (length fs) ++ "," ++ show (length ts) ++ "," ++ show reps ++ ","
            ++ show secs ++ "," ++ show (fromIntegral total / calls) ++ "," ++ showHex h "")
