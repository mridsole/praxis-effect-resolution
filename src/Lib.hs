{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# OPTIONS_GHC -fno-warn-partial-type-signatures #-}

module Lib where

import qualified Data.Set as Set
import Data.Set (Set)
import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import Data.Maybe (isJust, fromJust)
import Data.Bifunctor
import Control.Exception (assert)
import Debug.Trace (trace)
import Control.Monad.Loops (iterateWhile)
import Data.List (intercalate)

-- A literal effect
newtype Effect a = Eff a
    deriving (Eq, Ord, Show)

-- Variable standing for a set of effects.
newtype Variable a = Var a
    deriving (Eq, Ord, Show)

-- Something that might be a solution.
newtype Candidate var eff = Candidate (Map var (Set eff))
  deriving (Eq, Ord)

instance (Show var, Show eff) => Show (Candidate var eff) where
  show (Candidate candidatevs) =
    let
      -- Show each variable as show var ++ ": " ++ show (Set.toList values)
      -- Get a list of these, and intercalate with '\n'
      varstrings = fmap (
          \(var, effs) ->
            show var ++ ": " ++ show (Set.toList effs)
        ) $ Map.toList candidatevs
    in
      intercalate "\n" varstrings

-- Represents a union of a constant set V and a set of variables.
data Term var eff = Term (Set var) (Set eff)
  deriving (Eq, Ord)

instance (Show var, Show eff) => Show (Term var eff) where
  show (Term vars effs) =
    show (Set.toList effs) ++ " U " ++ show (Set.toList vars)

infix 2 +>
infix 2 <+
infix 1 :~:

vs <+ es = Term (Set.fromList vs) (Set.fromList es)
es +> vs = vs <+ es

-- General form of a constraint.
data Constraint var eff = Term var eff :~: Term var eff
  deriving (Eq, Ord)

instance (Show var, Show eff) => Show (Constraint var eff) where
  show (lhs :~: rhs) =
    show lhs ++ " = " ++ show rhs

-- | A system of constraints.
data ConstraintSystem v e = ConstraintSystem
  { _constraints :: Set (Constraint v e)
  , _variables :: Set v
  , _effects :: Set e
  }
  deriving (Eq, Ord)

instance (Show var, Show eff) => Show (ConstraintSystem var eff) where
  show (
    ConstraintSystem
      { _constraints = constraints
      , _variables = vars
      , _effects = effs
      }
    ) =
      let
        constraintsBlock = intercalate "\n" $
          fmap show (Set.toList constraints)
      in
        "Constraint System\n" ++
          "Variables: " ++ (show (Set.toList vars)) ++ "\n" ++
          "Effects: " ++ (show (Set.toList effs)) ++ "\n\n" ++
          constraintsBlock


-- | The trivial upper bound for a constraint system.
trivialUpperBound :: Set var -> Set eff -> Candidate var eff
trivialUpperBound vars effs = Candidate $ Map.fromSet (const effs) vars

-- TODO
-- refineUpperBound :: Candidate v e -> Candidate v e -> Candidate v e
-- refineUpperBound bound constr = fmap (Set.intersection constr) bound

-- | Generate equivalent constraint, but expressed other way around.
flipConstraint :: Constraint v e -> Constraint v e
flipConstraint (lhs :~: rhs) = (rhs :~: lhs)

-- | Construct a system of constraints, tracking the variables and effects.
fromConstraints :: (Ord v, Ord e) => Set (Constraint v e) -> ConstraintSystem v e
fromConstraints constraints =
  let
    constraintTermConsts (lhs :~: rhs) = Set.union (termConst lhs) (termConst rhs)
    constraintTermVars (lhs :~: rhs) = Set.union (termVars lhs) (termVars rhs)
    effs = foldr (Set.union . constraintTermConsts) Set.empty constraints
    vars = foldr (Set.union . constraintTermVars) Set.empty constraints
  in
    ConstraintSystem
      { _constraints = constraints
      , _variables = vars
      , _effects = effs
      }

-- | get the effects of a term.
termConst :: Ord var => Term var eff -> Set eff
termConst (Term vars effs) = effs

-- | Get the variables of a term.
termVars :: Ord var => Term var eff -> Set var
termVars (Term vars effs) = vars

-- | Does a variable appear in a term?
termHasVar :: Ord var => Term var eff -> var -> Bool
termHasVar (Term vars effs) var = Set.member var vars

-- | Is a term constant? (i.e. does it have no variables?)
termIsConst :: Ord var => Term var eff -> Bool
termIsConst (Term vars effs) = Set.null vars

constraintHasVar :: Ord var => Constraint var eff -> var -> Bool
constraintHasVar (lhs :~: rhs) v = termHasVar lhs v || termHasVar rhs v

-- | Fully evaluate a term.
-- evalTerm :: (Ord v, Ord e) => Term v e -> Candidate v e -> Set e
evalTerm term candidate =
  let
    Candidate candmap = candidate
    Term tvars teffs = term
    _ = assert (tvars `Set.isSubsetOf` Map.keysSet candmap) ()

    -- Compute union of variables.
    veffsAll = Map.foldr'
      Set.union
      Set.empty
      (Map.filterWithKey
        (\var veffs -> var `Set.member` tvars)
        candmap)
  in
    teffs `Set.union` veffsAll

-- | Check that a constraint is satisfied by a candidate.
checkConstraint (lhs :~: rhs) candidate =
  evalTerm lhs candidate == evalTerm rhs candidate

-- | Check that a system is satisfied by a candidate.
check :: (Ord v, Ord e) => ConstraintSystem v e -> Candidate v e -> Bool
check csys candidate =
  let
    constraints = (_constraints :: ConstraintSystem v e -> _) csys
  in
    Set.map
      (\constr -> checkConstraint constr candidate)
      constraints
    ==
      Set.singleton True

-- | Given a bound on the variables, compute the bound that bounds
-- all variables appearing in the given constraint.
constraintBound :: (Ord v, Ord e) => Constraint v e -> Candidate v e -> Set e
constraintBound (lhs :~: rhs) xbound =
  evalTerm lhs xbound `Set.intersection` evalTerm rhs xbound

-- | Construct a map from constraint to bounds for a system and a bound.
constraintBounds
  :: (Ord v, Ord e)
  => ConstraintSystem v e
  -> Candidate v e
  -> Map (Constraint v e) (Set e)

constraintBounds csys xbound =
  let
    constraints = (_constraints :: ConstraintSystem v e -> _) csys
    bounds = Map.fromList $ Set.toList $
      Set.map (\c -> (c, constraintBound c xbound)) constraints
  in
    bounds

-- | Refine a candidate upper bound.
refineBound
  :: (Ord v, Ord e)
  => ConstraintSystem v e -- The system of constraints.
  -> Candidate v e -- The current upper bound candidate.
  -> Candidate v e -- The new, refined upper bound candidate.

refineBound csys candidate =
  let
    -- Sanity check: csys and candidate should have exactly the same variables.
    Candidate candidatevs = candidate
    csysvars = (_variables :: ConstraintSystem v e -> _) csys
    _ = assert (csysvars == Map.keysSet candidatevs) ()

    -- Generate the per-constraint bounds using the current bounds candidate.
    cbounds = constraintBounds csys candidate

  in
    -- For each variable, collect the set of constraints in which it appears.
    -- Refine this variable's upper bound as the intersection of it's current
    -- upper bound with the intersection of all the cbounds for these
    -- constraints.
    Candidate $
    Map.mapWithKey (\var vbound ->
      let
        mentioned = Set.filter (flip constraintHasVar var) (Map.keysSet cbounds)
      in
        Map.foldr' Set.intersection vbound (Map.restrictKeys cbounds mentioned)
    )
    candidatevs

resolveStep
  :: (Eq v, Eq e, Ord v, Ord e)
  => ConstraintSystem v e
  -> Candidate v e
  -> Maybe (Either (Candidate v e) (Candidate v e))

resolveStep csys candidate =
  let
    newbound = refineBound csys candidate
  in
    case newbound == candidate of
      True -> case check csys newbound of
        True -> Just (Right newbound) -- Final solution.
        False -> Nothing -- No solution.
      False -> Just (Left newbound) -- Pending solution.

-- | Resolve a constraint system.
resolveConstraints
  :: (Eq v, Eq e, Ord v, Ord e)
  => ConstraintSystem v e
  -> Maybe (Candidate v e)

resolveConstraints csys =
  let
    vars = (_variables :: ConstraintSystem v e -> _) csys
    effs = (_effects :: ConstraintSystem v e -> _) csys

    -- Our starting point - could replace this with fmaximal.
    xboundinit = trivialUpperBound vars effs

    resolveStep' csys (Just (Left bound)) = resolveStep csys bound
    resolveStep' csys _ = undefined

    finished Nothing = True
    finished (Just (Right bound)) = True
    finished (Just (Left bound)) = False

    final = (
      filter finished $
        iterate (resolveStep' csys) (Just (Left xboundinit))
      ) !! 0
  in
    case final of
      Nothing -> Nothing
      Just (Right x) -> Just x

testSys = fromConstraints $ Set.fromList $
  [
    ["A","B","C"] +> ["x1"] :~: ["A","B","C"] +> [],
    ["C","D","E"] +> ["x2"] :~: ["C","D","E"] +> [],
    ["E"] +> ["x3"] :~: ["E"] +> [],
    ["C"] +> ["x4"] :~: ["C"] +> [],
    ["A"] +> ["x2", "x3"] :~: ["E"] +> ["x1"],
    [] +> ["x2"] :~: [] +> ["x5"],
    [] +> ["x5"] :~: [] +> ["x4"]
  ]

testSys2 = fromConstraints $ Set.fromList $
  [
    [1,2,3] +> [1] :~: [1,2,3] +> [],
    [3,4,5] +> [2] :~: [3,4,5] +> [],
    [5] +> [3] :~: [5] +> [],
    [3] +> [4] :~: [3] +> [],
    [1] +> [2,3] :~: [5] +> [1],
    [] +> [2] :~: [] +> [5],
    [] +> [5] :~: [] +> [4]
  ]
