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
  deriving (Eq, Show)
-- | Transforms a CoreExpr and keeps track if it has changed.
type Transform = [CoreContext] -> CoreSyn.CoreExpr -> TransformMonad CoreSyn.CoreExpr

-- Predicates for each of the context types
is_appfirst_ctx, is_appsecond_ctx, is_letbinding_ctx, is_letbody_ctx, is_lambdabody_ctx
 :: CoreContext -> Bool

is_appfirst_ctx AppFirst = True
is_appfirst_ctx _ = False

is_appsecond_ctx AppSecond = True
is_appsecond_ctx _ = False

is_letbinding_ctx LetBinding = True
is_letbinding_ctx _ = False

is_letbody_ctx LetBody = True
is_letbody_ctx _ = False

is_lambdabody_ctx LambdaBody = True
is_lambdabody_ctx _ = False
