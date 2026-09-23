-- | A Z3-backed 'Entailment' implemented with Liquid Fixpoint's SMT API.
module Data.CFTA.Refinement.LiquidFixpoint (
    integerDeclarations,
    withZ3,
    withZ3Assuming,
) where

import Control.Concurrent.MVar (modifyMVar, newMVar, withMVar)
import Control.Exception (bracket)
import Control.Monad.State.Lazy (runStateT)
import qualified Data.HashSet as HashSet
import Data.Maybe (fromMaybe)
import qualified Data.Text as Text

import Data.CFTA.Refinement (Entailment, Verdict (..), entailmentWithBindings)
import qualified Language.Fixpoint.Smt.Interface as SMT
import qualified Language.Fixpoint.Smt.Types as SMTTypes
import qualified Language.Fixpoint.Types as Fixpoint
import Language.Fixpoint.Types.Config (SMTSolver (Z3), defConfig, solver)

{- | Explicitly declare each supplied name as an integer.

'withZ3' and 'withZ3Assuming' declare every free name as an integer. When
actual terms at different positions share a name, each gets a separate solver
value with the sort of that name, or an integer when the name has no
declaration. So this helper only makes the integer sort explicit. Pass other
Liquid Fixpoint sorts directly to 'withZ3' or 'withZ3Assuming' when the
language needs them.
-}
integerDeclarations :: [String] -> [(Fixpoint.Symbol, Fixpoint.Sort)]
integerDeclarations = map (\name -> (Fixpoint.symbol name, Fixpoint.FInt))

-- | Run actions using one reusable Z3 process and a fixed declaration set.
withZ3 :: [(Fixpoint.Symbol, Fixpoint.Sort)] -> (Entailment -> IO a) -> IO a
withZ3 declarations = withZ3Assuming declarations []

{- | Run entailment queries under a fixed collection of ambient assumptions.

This models the surrounding Liquid typing environment. For example, an input
named @bufferLength@ may be declared as an integer and assumed equal to three;
position substitution can then prove that an index lies below that particular
buffer length. Each query declares as an integer every free name that the
declarations do not give a sort, including the value name @v@ and term symbols
that become actual values in a position substitution. Declare a name to give
it another sort.
-}
withZ3Assuming ::
    [(Fixpoint.Symbol, Fixpoint.Sort)] ->
    [Fixpoint.Pred] ->
    (Entailment -> IO a) ->
    IO a
withZ3Assuming given assumptions action =
    bracket acquire release $ \contextVar ->
        action (entailmentWithBindings $ query contextVar)
  where
    valueName = Fixpoint.symbol ("v" :: String)
    declarations
        | valueName `elem` map fst given = given
        | otherwise = (valueName, Fixpoint.FInt) : given
    known = HashSet.fromList $ map fst declarations

    config = defConfig{solver = Z3}

    acquire = newMVar =<< SMT.makeContextNoLog config
    release contextVar = withMVar contextVar SMT.cleanupContext

    query contextVar bindings antecedent consequent =
        case traverse freshDeclaration bindings of
            Nothing -> pure Unknown
            Just freshDeclarations -> do
                response <- modifyMVar contextVar $ \context -> do
                    let mentioned = foldMap Fixpoint.exprSymbolsSet (antecedent : consequent : assumptions)
                        declared = HashSet.union known $ HashSet.fromList $ map fst freshDeclarations
                        undeclared =
                            [(name, Fixpoint.FInt) | name <- HashSet.toList $ HashSet.difference mentioned declared]
                    (response, nextContext) <- runStateT (check (freshDeclarations <> undeclared)) context
                    case response of
                        -- Z3 answers the rejected command and then the check-sat.
                        -- Liquid Fixpoint reads only the first answer, so the next
                        -- query would read the second. A new process replaces the
                        -- old one. Each query sends its own declarations.
                        SMTTypes.Error _ -> do
                            SMT.cleanupContext nextContext
                            fresh <- SMT.makeContextNoLog config
                            pure (fresh, response)
                        _ -> pure (nextContext, response)
                responseVerdict response
      where
        check freshDeclarations = SMT.smtBracket "microcfta entailment" $ do
            SMT.smtDecls $ declarations <> freshDeclarations
            SMT.smtAssertDecl $
                Fixpoint.pAnd (assumptions <> [antecedent, Fixpoint.PNot consequent])
            SMT.command SMTTypes.CheckSat

        freshDeclaration (fresh, original)
            | fresh `elem` map fst declarations = Nothing
            | otherwise = Just (fresh, fromMaybe Fixpoint.FInt $ lookup original declarations)

        responseVerdict SMTTypes.Unsat = pure Yes
        responseVerdict SMTTypes.Sat = pure No
        responseVerdict SMTTypes.Unknown = pure Unknown
        responseVerdict (SMTTypes.Error message) =
            ioError . userError $ "Z3 rejected a microcfta query: " <> Text.unpack message
        responseVerdict response =
            ioError . userError $ "Unexpected Z3 response: " <> show response
