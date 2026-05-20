
import LeanFomega.Util
import LeanFomega.Term
open LeanSubst

namespace LeanFomega

inductive Ty.Red : Ty -> Ty -> Prop where
| beta {K : Kind} : Ty.Red ((λ[K] b) • t) b[su t::+0]
| lam_congr : Ty.Red t t' -> Ty.Red (λ[K1] t) (λ[K2] t')
| app_congr1 : Ty.Red f f' -> Ty.Red (f • a) (f' • a)
| app_congr2 : Ty.Red a a' -> Ty.Red (f • a) (f • a')
| all_congr : Ty.Red P P' -> Ty.Red (∀[K1] P) (∀[K2] P')
| arrow_congr1 : Ty.Red A A' -> Ty.Red (A -:> B) (A' -:> B)
| arrow_congr2 : Ty.Red B B' -> Ty.Red (A -:> B) (A -:> B')

infix:160 " ~t> " => Ty.Red
infix:160 " ~t>* " => Star Ty.Red
infix:160 " =t= " => Conv Ty.Red

end LeanFomega
