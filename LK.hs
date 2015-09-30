import Data.List (intersect)

data Formula = Var     Char
             | Not     Formula
             | Or      Formula Formula
             | And     Formula Formula
             | Implies Formula Formula
               deriving (Show, Eq)

-- Using lists in favor of bags; should be OK as the order is ignored.
type Sequent = ([Formula], [Formula])

data Rule = AlphaRule Sequent
          | BetaRule  Sequent Sequent
            deriving Show

isAtomic :: Formula -> Bool
isAtomic (Var p) = True
isAtomic _       = False

isAxiom :: Sequent -> Bool
isAxiom (antecedents, succedents) = filter isAtomic formulas /= []
    where formulas = intersect antecedents succedents

rule :: Sequent -> Maybe Rule

rule (gamma, ((Not phi):delta)) = Just $ AlphaRule ((phi:gamma), delta)
rule (((Not phi):gamma), delta) = Just $ AlphaRule (gamma, (phi:delta))

rule (gamma, ((Or phi psi):delta)) = Just $ AlphaRule (gamma, (phi:psi:delta))
rule (((Or phi psi):gamma), delta) = Just $ BetaRule  ((phi:gamma), delta) ((psi:gamma), delta)

rule (gamma, ((And phi psi):delta)) = Just $ BetaRule  (gamma, (phi:delta)) (gamma, (psi:delta))
rule (((And phi psi):gamma), delta) = Just $ AlphaRule ((phi:psi:gamma), delta)

rule (gamma, ((Implies phi psi):delta)) = Just $ AlphaRule ((phi:gamma), (psi:delta))
rule (((Implies phi psi):gamma), delta) = Just $ BetaRule  (gamma, (phi:delta)) ((psi:gamma), delta)

