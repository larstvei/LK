import Data.List (intersect)

data Formula = Var     Char
             | Not     Formula
             | Or      Formula Formula
             | And     Formula Formula
             | Implies Formula Formula deriving (Show, Eq)

-- Using lists in favor of bags; should be OK as the order is ignored.
type Sequent = ([Formula], [Formula])

data Rule = AlphaRule Sequent
          | BetaRule  Sequent Sequent deriving Show

isAtomic :: Formula -> Bool
isAtomic (Var p) = True
isAtomic _       = False

isAxiom :: Sequent -> Bool
isAxiom (antecedents, succedents) = filter isAtomic formulas /= []
    where formulas = intersect antecedents succedents

rule :: Sequent -> Maybe Rule
rule (gamma, delta)
    | (not . null) phi =
        Just $ case phi of
                 (Not phi:gamma)       -> AlphaRule (gamma, (phi:delta))
                 (Or phi psi:gamma)      -> BetaRule  ((phi:gamma), delta) ((psi:gamma), delta)
                 (And phi psi:gamma)     -> AlphaRule ((phi:psi:gamma), delta)
                 (Implies phi psi:gamma) -> BetaRule  (gamma, (phi:delta)) ((psi:gamma), delta)
    | (not . null) psi =
        Just $ case psi of
                 (Not phi:delta)       -> AlphaRule ((phi:gamma), delta)
                 (Or phi psi:delta)      -> AlphaRule (gamma, (phi:psi:delta))
                 (And phi psi:delta)     -> BetaRule  (gamma, (phi:delta)) (gamma, (psi:delta))
                 (Implies phi psi:delta) -> AlphaRule ((phi:gamma), (psi:delta))
    | otherwise = Nothing
    where phi = filter (not . isAtomic) gamma
          psi = filter (not . isAtomic) delta
