module Main where


import Prelude
import System.Environment (getArgs)

import qualified Data.ByteString.Char8 as B
import Data.Parse.DimacsCNF
import Data.Parse.DRAT
import qualified Data.CNF as C
import qualified Data.DRAT as D



data Prod a b =
   Pair a b


type List a = [a]


list_rect :: a2 -> (a1 -> (List a1) -> a2 -> a2) -> (List a1) -> a2
list_rect f f0 l =
  case l of {
   [] -> f;
   (:) y l0 -> f0 y l0 (list_rect f f0 l0)}

list_rec :: a2 -> (a1 -> (List a1) -> a2 -> a2) -> (List a1) -> a2
list_rec =
  list_rect

remove_all_occ :: (a1 -> a1 -> Bool) -> a1 -> (List a1) -> List a1
remove_all_occ a_eq_dec x l =
  case l of {
   [] -> [];
   (:) y tl ->
    case a_eq_dec x y of {
     True -> remove_all_occ a_eq_dec x tl;
     False -> (:) y (remove_all_occ a_eq_dec x tl)}}

type R = Int

data Literal =
   Litp R
 | Litn R
 deriving (Eq)

literal_rec :: (R -> a1) -> (R -> a1) -> Literal -> a1
literal_rec f f0 l =
  case l of {
   Litp x -> f x;
   Litn x -> f0 x}


type Clause = List Literal

type Formula = List Clause


type Pinterpretation = List Literal

psatL_dec :: Pinterpretation -> Literal -> Bool
psatL_dec i l = l `elem` i

psatC_dec :: Pinterpretation -> Clause -> Bool
psatC_dec i' c = Prelude.any (psatL_dec i') c

compl :: Literal -> Literal
compl l =
  case l of {
   Litp v -> Litn v;
   Litn v -> Litp v}

pfalL_dec :: Pinterpretation -> Literal -> Bool
pfalL_dec i l = compl l `elem` i

removeFalsifiedLiterals :: Clause -> Pinterpretation -> Clause
removeFalsifiedLiterals c i = filter (not . pfalL_dec i) c

reduct :: Formula -> Pinterpretation -> Formula
reduct f i =
  map (\c -> removeFalsifiedLiterals c i)
    (filter (\c ->
      case psatC_dec i c of {
       True -> False;
       False -> True}) f)

unit_rule_step :: Formula -> Literal -> Formula
unit_rule_step f l =
  reduct f [l]

get_unit :: Formula -> Maybe Literal
get_unit f =
  case f of {
   [] -> Nothing;
   (:) c cs ->
    case c of {
     [] -> get_unit cs;
     (:) l l0 ->
      case l0 of {
       [] -> Just l;
       (:) l1 l2 -> get_unit cs}}}

exhaustive_unit_propagation :: Formula -> Formula
exhaustive_unit_propagation f =
  case get_unit f of {
   Just l -> exhaustive_unit_propagation (unit_rule_step f l);
   Nothing -> f}

complC :: Clause -> Formula
complC c =
  map (\l -> (:) (compl l) []) c

contains_empty_clause :: Formula -> Bool
contains_empty_clause f =
  case f of {
   [] -> False;
   (:) c cs ->
    case c of {
     [] -> True;
     (:) l l0 -> contains_empty_clause cs}}

rUP_check :: Formula -> Clause -> Bool
rUP_check f c =
  contains_empty_clause (exhaustive_unit_propagation ((++) (complC c) f))

data Label =
   Add
 | Del

type Labeled_clause = Prod Label Clause

type Labeled_clause_list = List Labeled_clause

associated_formula :: Formula -> Labeled_clause_list -> Formula
associated_formula f d =
  case d of {
   [] -> f;
   (:) l ds ->
    case l of {
     Pair l0 c ->
      case l0 of {
       Add -> (:) c (associated_formula f ds);
       Del -> remove_all_occ (==) c (associated_formula f ds)}}}

resolve :: Clause -> Clause -> Literal -> Clause
resolve c d l =
  (++) (remove_all_occ (==) l c) (remove_all_occ (==) (compl l) d)


rAT2_check :: Formula -> Clause -> Literal -> Bool
rAT2_check f c l =
  if (l `elem` c)
  then
    (all (\d -> rUP_check f (resolve c d l))
      (filter (compl l `elem`)
        f))
  else False

redundancy_check :: Formula -> Clause -> Bool
redundancy_check f c =
  case c of {
   [] -> rUP_check f c;
   (:) l ls -> (rUP_check f c) || (rAT2_check f ((:) l ls) l)}

check_a_rat_derivation :: Formula -> Labeled_clause_list -> Bool
check_a_rat_derivation f c =
  case c of {
   [] -> True;
   (:) l d ->
    case l of {
     Pair l0 c0 ->
      case l0 of {
       Add ->
         check_a_rat_derivation f d && (redundancy_check (associated_formula f d) c0);
       Del -> check_a_rat_derivation f d}}}

check_a_rat_refutation :: Formula -> Labeled_clause_list -> Bool
check_a_rat_refutation f c =
  case [] `elem` associated_formula f c of {
   True -> check_a_rat_derivation f c;
   False -> False}


main = do
  args <- getArgs

  let cnfFilename = args!!0
      proofFilename = args!!1

  cnfStr <- B.readFile cnfFilename
  proofStr <- B.readFile proofFilename

  let c = convertFormula (parseCNF cnfStr)
      p = convertProof (parseProof proofStr)



  let pR = check_a_rat_refutation c p

  putStrLn $ if pR then "s VERIFIED" else "s NOT VERIFIED"

convertLiteral :: Int -> Literal
convertLiteral x = if x > 0 then Litp x else Litn (abs x)

convertFormula :: C.DimacsCNF -> Formula
convertFormula = map (map convertLiteral) . C.clauses

convertProof :: D.ProofSequence -> Labeled_clause_list
convertProof = map convertCl . D.pClauses
  where
    convertCl (op, cl) = let op' = if op == D.ADD then Add else Del in Pair op' (map convertLiteral cl)
