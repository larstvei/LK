import Data.Ord  (comparing)
import Data.Char (toUpper)
import Data.List (delete, intercalate, intersect, minimumBy)

data Formula = Var     Char
             | Not     Formula
             | Or      Formula Formula
             | And     Formula Formula
             | Implies Formula Formula
               deriving Eq

-- Using lists in favor of bags; should be OK as the order is ignored.
type Sequent = ([Formula], [Formula])

type Label = String

data Rule = AlphaRule Sequent Label
          | BetaRule  Sequent Sequent Label deriving Show

isAtomic :: Formula -> Bool
isAtomic (Var p) = True
isAtomic _       = False

isAxiom :: Sequent -> Bool
isAxiom (gamma, delta) = filter isAtomic formulas /= []
    where formulas = intersect gamma delta

ordGamma :: Formula -> Integer
ordGamma phi = case phi of
               (Not       _) -> 0
               (And     _ _) -> 0
               (Or      _ _) -> 1
               (Implies _ _) -> 1
               (Var       _) -> 10

ordDelta :: Formula -> Integer
ordDelta phi = case phi of
               (Not       _) -> 0
               (Or      _ _) -> 0
               (Implies _ _) -> 0
               (And     _ _) -> 1
               (Var       _) -> 10

applyGammaRule :: Formula -> Sequent -> Maybe Rule
applyGammaRule phi (gamma,delta) =
    case phi of
      Not phi       -> Just $ AlphaRule (gamma, (phi:delta))            "L$\\neg$"
      And phi psi     -> Just $ AlphaRule ((phi:psi:gamma), delta)          "L$\\land$"
      Or phi psi      -> Just $ BetaRule  ((phi:gamma), delta) ((psi:gamma), delta) "L$\\lor$"
      Implies phi psi -> Just $ BetaRule  (gamma, (phi:delta)) ((psi:gamma), delta) "L$\\to$"
      _           -> Nothing

applyDeltaRule :: Formula -> Sequent -> Maybe Rule
applyDeltaRule phi (gamma,delta) =
    case phi of
      Not phi       -> Just $ AlphaRule ((phi:gamma), delta)            "R$\\neg$"
      Or phi psi      -> Just $ AlphaRule (gamma, (phi:psi:delta))          "R$\\lor$"
      Implies phi psi -> Just $ AlphaRule ((phi:gamma), (psi:delta))        "R$\\to$"
      And phi psi     -> Just $ BetaRule  (gamma, (phi:delta)) (gamma, (psi:delta)) "R$\\land$"
      _           -> Nothing

chooseRule :: Sequent -> Maybe Rule
chooseRule (gamma, delta) | isAxiom (gamma,delta) = Nothing
                  | s == "gamma"  = applyGammaRule phi (delete phi gamma, delta)
                  | s == "delta"  = applyDeltaRule phi (gamma, delete phi delta)
    where g            = zip3 (map ordGamma gamma) gamma (repeat "gamma")
          d            = zip3 (map ordDelta delta) delta (repeat "delta")
          (_, phi, s)    = minimumBy (comparing fst') (g++d)
          fst' (a,_,_) = a

data DeductionTree = Leaf Sequent
                   | Alpha Sequent Label DeductionTree
                   | Beta  Sequent Label DeductionTree DeductionTree

buildTree :: Sequent -> DeductionTree
buildTree sequent = case chooseRule sequent of
                      Just (AlphaRule seq label) ->
                          Alpha sequent label (buildTree seq)
                      Just (BetaRule seq1 seq2 label) ->
                          Beta sequent label (buildTree seq1) (buildTree seq2)
                      Nothing -> Leaf sequent

leaves :: DeductionTree -> [Sequent]
leaves (Leaf sequent) = [sequent]
leaves (Alpha _  _ tree) = leaves tree
leaves (Beta  _  _ tree1 tree2) = leaves tree1 ++ leaves tree2

isValidSequent :: Sequent -> Bool
isValidSequent seq = all isAxiom $ leaves $ buildTree seq

isValid :: Formula -> Bool
isValid phi = isValidSequent ([], [phi])

-- Show/Read functions

showSequent :: Sequent -> String
showSequent (gamma,delta) = sl gamma ++ vd ++ sl delta
    where sl = intercalate ", " . map show
          vd | isAxiom (gamma,delta) = " \\stackrel{\\times}{\\vdash} "
             | otherwise = " \\vdash "

instance Show Formula where
    show = showFormula

showFormula :: Formula -> String
showFormula phi = case phi of
                  (Var     p)   -> [toUpper p]
                  (Not     phi)   -> "\\neg " ++ showFormula phi
                  (Or      phi psi) -> paren $ showFormula phi ++ " \\lor " ++ showFormula psi
                  (And     phi psi) -> paren $ showFormula phi ++ " \\land " ++ showFormula psi
                  (Implies phi psi) -> paren $ showFormula phi ++ " \\to " ++ showFormula psi
    where paren s = "(" ++ s ++ ")"

readFormula :: String -> Formula
readFormula xs = phi
    where (phi, _) = readFormula' xs

readFormula' :: String -> (Formula, String)
readFormula' [x]    = ((Var x), [])
readFormula' (x:xs) | member x "pqrst" = ((Var x), xs)
                    | x == 'N' = ((Not     phi),   r)
                    | x == 'O' = ((Or      phi psi), r')
                    | x == 'A' = ((And     phi psi), r')
                    | x == 'I' = ((Implies phi psi), r')
    where (phi, r)   = readFormula' xs
          (psi, r')  = readFormula' r
          member x = (not . null . filter (==x))

instance Show DeductionTree where
    show = showTree

showTree :: DeductionTree -> String
showTree node = wrapProoftree $ reverseLines $ showTree' node
    where showTree' node =
              case node of
                (Leaf (gamma,delta)) ->
                    [ax $ showSequent (gamma,delta)]
                (Alpha (gamma,delta) l tree) ->
                    (label l $ un $ showSequent (gamma,delta)) : showTree' tree
                (Beta  (gamma,delta) l tree1 tree2) ->
                    (label l $ bi $ showSequent (gamma,delta)) :
                        (showTree' tree1 ++ showTree' tree2)
          ax s = "\\AxiomC{$"     ++ s ++ "$}"
          un s = "\\UnaryInfC{$"  ++ s ++ "$}"
          bi s = "\\BinaryInfC{$" ++ s ++ "$}"
          label l = ((++) $ "\\RightLabel{\\scriptsize{" ++ l ++ "}}\n")
          reverseLines    = unlines . reverse
          wrapProoftree p = "\\begin{prooftree}\n" ++ p ++ "\\end{prooftree}"
