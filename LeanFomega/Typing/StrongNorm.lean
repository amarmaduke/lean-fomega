
import LeanSubst
import LeanFomega.Typing
import LeanFomega.Typing.Substitute
open LeanSubst

namespace LeanFomega

def TSet := List Kind -> List Ty -> Term -> Ty -> Prop
def TSet.empty : TSet := λ _ _ _ _ => False
def TRed := List Kind -> List Ty -> Term -> Term -> Prop

def LR := List Kind -> List Ty -> Term -> Prop

def ℛ (S : LR) : LR
| Δ, Γ1, t => ∀ {r Γ2}, Γ1 -⟨r⟩> Γ2 -> S Δ Γ2 t[r]

mutual
  inductive Typing.SnNor : LR -> TSet
  | lam :
    ℛ S1 Δ Γ (λ[A] t) ->
    SnNor S2 Δ (A::Γ) t B ->
    SnNor S1 Δ Γ (λ[A] t) (A -:> B)
  | tlam :
    SnNor S2 (K::Δ) Γ⟨.add 1⟩ t P ->
    SnNor S1 Δ Γ (Λ[K] t) (∀[K] P)
  | neu :
    SnNeu S Δ Γ t A ->
    SnNor S Δ Γ t A
  | red :
    SnRed S Δ Γ t t' ->
    SnNor S Δ Γ t' A ->
    SnNor S Δ Γ t A

  inductive Typing.SnNeu : LR -> TSet
  | var :
    Γ[x]? = some A ->
    SnNeu S Δ Γ #x A
  | app :
    SnNeu S1 Δ Γ f (A -:> B) ->
    SnNor S2 Δ Γ a A ->
    SnNeu S3 Δ Γ (f • a) B
  | tapp :
    SnNeu S1 Δ Γ f (∀[K] P) ->
    P' = P[su a::+0] ->
    SnNeu S3 Δ Γ (f •[a]) P'

  inductive Typing.SnRed : LR -> TRed
  | beta :
    SnNor S1 Δ Γ t A ->
    SnRed S2 Δ Γ ((λ[A] b) • t) b[su t::+0]
  | tbeta :
    SnRed S Δ Γ ((Λ[K] b) •[t]) b[su t::+0:Ty]
  | app :
    SnRed S1 Δ Γ f f' ->
    SnRed S2 Δ Γ (f • a) (f' • a)
  | tapp :
    SnRed S1 Δ Γ f f' ->
    SnRed S2 Δ Γ (f •[a]) (f' •[a])
end

mutual
  theorem Typing.SnNor.rename {Γ1 Γ2 : List Ty} (m : Γ1 -⟨r⟩> Γ2)
    : SnNor S Δ Γ1 t A -> SnNor S Δ Γ2 t[r] A := sorry

  theorem Typing.SnNeu.rename {Γ1 Γ2 : List Ty} (m : Γ1 -⟨r⟩> Γ2)
    : SnNeu S Δ Γ1 t A -> SnNeu S Δ Γ2 t[r] A := sorry

  theorem Typing.SnRed.rename {Γ1 Γ2 : List Ty} (m : Γ1 -⟨r⟩> Γ2)
    : SnRed S Δ Γ1 t t' -> SnRed S Δ Γ2 t[r] t'[r] := sorry
end

@[simp]
def 𝒱 : Ty -> List Kind -> List Ty -> Term -> Prop
| A -:> B, Δ, Γ, λ[_] t => ∀ {a}, Typing.SnNor (𝒱 A) Δ Γ a A -> Typing.SnNor (𝒱 B) Δ Γ t[su a::+0] B
| _, _, _, _ => False

structure Typing.SemSubst (Δ : List Kind) (Γ1 Γ2 : List Ty) (σ : Subst Term) where
  act : ∀ {i T}, Γ1[i]? = some T -> SnNor (𝒱 T) Δ Γ2 (σ.act i) T

notation:35 Δ " ⊢ " Γ1:35 " -⟦" σ "⟧> " Γ2:35 => Typing.SemSubst Δ Γ1 Γ2 σ

theorem Typing.SemSubst.lift (m : Δ ⊢ Γ1 -⟦σ⟧> Γ2) A : Δ ⊢ A::Γ1 -⟦σ.lift⟧> A::Γ2 := sorry

theorem Typing.SemSubst.compose (m1 : Δ ⊢ Γ1 -⟦σ⟧> Γ2) (m2 : Γ2 -⟨r⟩> Γ3)
  : Δ ⊢ Γ1 -⟦σ ∘ r.to⟧> Γ3 := sorry

@[simp]
def SemanticTyping (Δ : List Kind) (Γ1 : List Ty) (t : Term) (A : Ty) :=
  ∀ {σ Γ2}, Δ ⊢ Γ1 -⟦σ⟧> Γ2 -> Typing.SnNor (𝒱 A) Δ Γ2 t[σ] A

notation:170 Δ:170 "&" Γ:170 " ⊨ " t:170 " : " A:170 => SemanticTyping Δ Γ t A

theorem Typing.fundamental : Δ&Γ ⊢ t : A -> Δ&Γ ⊨ t : A
| var j1 j2, σ, Γ2, h => sorry
| lam j1 j2, σ, Γ2, h => sorry
| app j1 j2, σ, Γ2, h => sorry
| tlam j, σ, Γ2, h => sorry
| tapp j1 j2 e, σ, Γ2, h => sorry

end LeanFomega
