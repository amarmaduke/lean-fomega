
import LeanFomega.Term
import LeanFomega.Reduction
open LeanSubst

namespace LeanFomega

inductive Kinding : List Kind -> Ty -> Kind -> Prop where
| var :
  Δ[x]? = some K ->
  Kinding Δ t#x K
| lam :
  Kinding (A::Δ) t B ->
  Kinding Δ (λ[A] t) (A -:> B)
| app :
  Kinding Δ f (A -:> B) ->
  Kinding Δ a A ->
  Kinding Δ (f • a) B
| all :
  Kinding (K::Δ) P ★ ->
  Kinding Δ (∀[K] P) ★
| arrow :
  Kinding Δ A ★ ->
  Kinding Δ B ★ ->
  Kinding Δ (A -:> B) ★

notation:170 Δ:170 " ⊢ₖ " A:170 " : " K:170 => Kinding Δ A K

inductive Typing : List Kind -> List Ty -> Term -> Ty -> Prop where
| var :
  Γ[x]? = some T ->
  Δ ⊢ₖ T : ★ ->
  Typing Δ Γ #x T
| lam :
  Δ ⊢ₖ A : ★ ->
  Typing Δ (A::Γ) t B ->
  Typing Δ Γ (λ[A] t) (A -:> B)
| app :
  Typing Δ Γ f (A -:> B) ->
  Typing Δ Γ a A ->
  Typing Δ Γ (f • a) B
| tlam :
  Typing (K::Δ) Γ⟨.add 1⟩ t P ->
  Typing Δ Γ (Λ[K] t) (∀[K] P)
| tapp :
  Typing Δ Γ f (∀[K] P) ->
  Δ ⊢ₖ a : K ->
  P' = P[su a::+0] ->
  Typing Δ Γ (f •[a]) P'
| conv :
  Typing Δ Γ t A ->
  A =t= B ->
  Δ ⊢ₖ B : K ->
  Typing Δ Γ t B

notation:170 Δ:170 "&" Γ:170 " ⊢ " t:170 " : " A:170 => Typing Δ Γ t A

end LeanFomega
