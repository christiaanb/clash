module CLasH.Normalize.NormalizeTypes where

-- Standard modules
import qualified Control.Monad.Trans.Writer as Writer
import qualified Data.Monoid as Monoid

-- GHC API
import qualified CoreSyn

-- Local imports
import CLasH.Translator.TranslatorTypes

-- Wrap a writer around a TranslatorSession, to run a single transformation
-- over a single expression and track if the expression was changed.
type TransformMonad = Writer.WriterT Monoid.Any TranslatorSession

-- | In what context does a core expression occur?
data CoreContext = AppFirst        -- ^ The expression is the first
                                   -- argument of an application (i.e.,
                                   -- it is applied)
                 | AppSecond       -- ^ The expression is the second
                                   --   argument of an application
                                   --   (i.e., something is applied to it)
                 | LetBinding      -- ^ The expression is bound in a
                                   --   (recursive or non-recursive) let
                                   --   expression.
                 | LetBody         -- ^ The expression is the body of a
                                   --   let expression
                 | LambdaBody      -- ^ The expression is the body of a
                                   --   lambda abstraction
                 | Other           -- ^ Another context
-- | Transforms a CoreExpr and keeps track if it has changed.
type Transform = [CoreContext] -> CoreSyn.CoreExpr -> TransformMonad CoreSyn.CoreExpr
