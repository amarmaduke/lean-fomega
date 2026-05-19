
import LeanSubst
import LeanFomega.Typing
import LeanFomega.Typing.Substitute
import LeanFomega.Kinding.StrongNorm
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

notation:160 Δ:170 " ⊢ " Γ1:170 " -⟦" σ "⟧> " Γ2:170 => Typing.SemSubst Δ Γ1 Γ2 σ

theorem Typing.SemSubst.id : Δ ⊢ X -⟦+0⟧> X := sorry

theorem Typing.SemSubst.lift (m : Δ ⊢ Γ1 -⟦σ⟧> Γ2) A : Δ ⊢ (A::Γ1) -⟦σ.lift⟧> (A::Γ2) := sorry

theorem Typing.SemSubst.compose (m1 : Δ ⊢ Γ1 -⟦σ⟧> Γ2) (m2 : Γ2 -⟨r⟩> Γ3)
  : Δ ⊢ Γ1 -⟦σ ∘ r.to⟧> Γ3 := sorry

theorem Typing.SemSubst.hcompose :
  Δ1 ⊢ A -⟦σ⟧> B ->
  Δ1 -⟨r⟩> Δ2 ->
  Δ2 ⊢ A⟨r⟩ -⟦σ ◾ @r.to Ty⟧> B⟨r⟩
:= sorry

@[simp]
def SemanticTyping (Δ : List Kind) (Γ1 : List Ty) (t : Term) (A : Ty) :=
  ∀ {σ Γ2}, Δ ⊢ Γ1 -⟦σ⟧> Γ2 -> Typing.SnNor (𝒱 A) Δ Γ2 t[σ] A

notation:170 Δ:170 "&" Γ:170 " ⊨ " t:170 " : " A:170 => SemanticTyping Δ Γ t A

theorem SemanticTyping.tapp :
  V = 𝒱 (∀[K] P) ->
  T = (∀[K] P) ->
  Typing.SnNor V Δ Γ f T ->
  Kinding.SnNor (𝒱ₖ K) Δ a K ->
  Typing.SnNor (𝒱 P[su a::+0]) Δ Γ (f •[a]) P[su a::+0]
:= sorry

theorem Typing.fundamental : Δ&Γ ⊢ t : A -> Δ&Γ ⊨ t : A
| var j1 j2, σ, Γ2, h => sorry
| lam j1 j2, σ, Γ2, h => sorry
| app j1 j2, σ, Γ2, h =>
  let j1' := j1.fundamental h
  sorry
| tlam (K := K) j, σ, Γ2, h =>
  let h' : (K :: Δ) ⊢ Γ⟨.add 1⟩ -⟦σ ◾ +1⟧> Γ2⟨.add 1⟩ := h.hcompose (Δ2 := K::Δ) .succ
  let j' := j.fundamental h'
  .tlam j'
| tapp j1 j2 e, σ, Γ2, h =>
  let j1' := j1.fundamental h
  let j2' := j2.fundamental .id
  SemanticTyping.tapp rfl rfl j1' j2' |> cast (by simp [e])

theorem Typing.SnNeu.consistency_lemma :
  Γ = [] ->
  SnNeu T Δ Γ t A ->
  Δ&Γ ⊢ t : X ->
  False
| e, .var h, j => by grind
| e, .app fn an, (.app fj aj) => fn.consistency_lemma e fj
| e1, .tapp fn e2, (.tapp fj aj e3) => fn.consistency_lemma e1 fj

theorem Typing.SnNor.consistency_lemma :
  Γ = [] ->
  SnNor T Δ Γ t A ->
  Δ&Γ ⊢ t : (∀[★] t#0) ->
  False
| e, .tlam (.neu tn), .tlam tj => tn.consistency_lemma (by simp [e]) tj
| e, .tlam (.red tr tn), .tlam tj => tn.consistency_lemma (by simp [e]) sorry
| e, .neu tn, j3 => tn.consistency_lemma e j3
| e, .red tr tn, j3 => tn.consistency_lemma e sorry

theorem Typing.consistency : ¬ (Δ&[] ⊢ t : (∀[★] t#0))
| j => SnNor.consistency_lemma rfl (j.fundamental $ SemSubst.id) (j |> cast (by simp))

end LeanFomega
