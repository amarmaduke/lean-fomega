
import LeanSubst
import LeanFomega.Typing
import LeanFomega.Kinding.Substitute
open LeanSubst

namespace LeanFomega

def KSet := List Kind -> Ty -> Kind -> Prop
def KSet.empty : KSet := λ _ _ _ => False
def KRed := List Kind -> Ty -> Ty -> Prop

def ℛₖ (S : List Kind -> Ty -> Prop) : List Kind -> Ty -> Prop
| Δ1, t => ∀ {r Δ2}, Δ1 -⟨r⟩> Δ2 -> S Δ2 t[r]

mutual
  inductive Kinding.SnNor : (List Kind -> Ty -> Prop) -> KSet
  | lam :
    ℛₖ S1 Δ (λ[A] t) ->
    SnNor S2 (A::Δ) t B ->
    SnNor S1 Δ (λ[A] t) (A -:> B)
  | all :
    SnNor S (A::Δ) t ★ ->
    SnNor S Δ (∀[A] t) ★
  | arrow :
    SnNor S Δ A ★ ->
    SnNor S Δ B ★ ->
    SnNor S Δ (A -:> B) ★
  | neu :
    SnNeu S Δ A K ->
    SnNor S Δ A K
  | red :
    SnRed Δ S A A' ->
    SnNor Δ S A' K ->
    SnNor Δ S A K

  inductive Kinding.SnNeu : (List Kind -> Ty -> Prop) -> KSet
  | var :
    Δ[x]? = some K ->
    SnNeu S Δ t#x K
  | app :
    SnNeu S1 Δ f (A -:> B) ->
    SnNor S2 Δ a A ->
    SnNeu S3 Δ (f • a) B

  inductive Kinding.SnRed : (List Kind -> Ty -> Prop) -> KRed
  | beta :
    SnNor S1 Δ t A ->
    SnRed S2 Δ ((λ[A] b) • t) b[su t::+0]
  | app :
    SnRed S1 Δ f f' ->
    SnRed S2 Δ (f • a) (f' • a)
end

mutual
  theorem Kinding.SnNor.rename (m : Δ1 -⟨r⟩> Δ2) : SnNor S Δ1 A K -> SnNor S Δ2 A[r] K := sorry

  theorem Kinding.SnNeu.rename (m : Δ1 -⟨r⟩> Δ2) : SnNeu S Δ1 A K -> SnNeu S Δ2 A[r] K := sorry

  theorem Kinding.SnRed.rename (m : Δ1 -⟨r⟩> Δ2) : SnRed S Δ1 A B -> SnRed S Δ2 A[r] B[r] := sorry
end

@[simp]
def 𝒱ₖ : Kind -> List Kind -> Ty -> Prop
| A -:> B, Δ, λ[_] t => ∀ {a}, Kinding.SnNor (𝒱ₖ A) Δ a A -> Kinding.SnNor (𝒱ₖ B) Δ t[su a::+0] B
| _, _, _ => False

structure Kinding.SemSubst (Δ1 Δ2 : List Kind) (σ : Subst Ty) where
  act : ∀ {i T}, Δ1[i]? = some T -> SnNor (𝒱ₖ T) Δ2 (σ.act i) T

notation:35 Γ:35 " -⟦" σ "⟧> " Δ:35 => Kinding.SemSubst Γ Δ σ

theorem Kinding.SemSubst.id : Δ -⟦+0⟧> Δ := sorry

theorem Kinding.SemSubst.lift (m : Γ -⟦σ⟧> Δ) A : A::Γ -⟦σ.lift⟧> A::Δ := sorry

theorem Kinding.SemSubst.compose (m1 : Γ -⟦σ⟧> Δ) (m2 : Δ -⟨r⟩> Ξ) : Γ -⟦σ ∘ r.to⟧> Ξ := sorry

@[simp]
def SemanticKinding (Δ1 : List Kind) (A : Ty) (K : Kind) :=
  ∀ {σ Δ2}, Δ1 -⟦σ⟧> Δ2 -> Kinding.SnNor (𝒱ₖ K) Δ2 A[σ] K

notation:170 Γ:170 " ⊨ₖ " t:170 " : " A:170 => SemanticKinding Γ t A

theorem Kinding.fundamental : Δ ⊢ₖ A : K -> Δ ⊨ₖ A : K
| var j, σ, Δ2, h => sorry
| lam j, σ, Δ2, h => sorry
| app j1 j2, σ, Δ2, h => sorry
| all j, σ, Δ2, h => .all $ j.fundamental $ h.lift _
| arrow j1 j2, σ, Δ2, h => .arrow (j1.fundamental h) (j2.fundamental h)

end LeanFomega
