import Lean

namespace Lean.Expr

/-- Runs `f` on each immediate child of the given expression. -/
def traverseChildren [Applicative M] (f : Expr → M Expr) : Expr → M Expr
| e@(forallE _ d b _) => pure e.updateForallE! <*> f d <*> f b
| e@(lam _ d b _)     => pure e.updateLambdaE! <*> f d <*> f b
| e@(mdata _ b _)     => e.updateMData! <$> f b
| e@(letE _ t v b _)  => pure e.updateLet! <*> f t <*> f v <*> f b
| e@(app l r _)       => pure e.updateApp! <*> f l <*> f r
| e@(proj _ _ b _)    => e.updateProj! <$> f b
| e                   => pure e

end Lean.Expr
