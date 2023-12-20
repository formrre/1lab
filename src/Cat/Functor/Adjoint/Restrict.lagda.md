```agda

open import Cat.Functor.Adjoint
open import Cat.Prelude
open import Cat.Functor.Properties
module Cat.Functor.Adjoint.Restrict {o}{ℓ}{o'}{ℓ'}
 {C C' : Precategory o ℓ} {D D' : Precategory o' ℓ'} {L' : Functor C' D'}{R' : _} (adj : L' ⊣ R')
 {iC : Functor C C'}{iD : Functor D D'}
 {L : Functor C D}{R : Functor D C}
 {ffIC : is-fully-faithful iC}
 {ffID : is-fully-faithful iD}
 where

open import Cat.Functor.Naturality
open import Cat.Functor.Adjoint.Hom

hom-equiv→adjoints : ∀{o ℓ o' ℓ'} {C : Precategory o ℓ}{D : Precategory o' ℓ'}
 → {L : Functor D C} {R : Functor C D}
 → (eqv : ∀{x}{y} → Precategory.Hom C (Functor.F₀ L x) y ≃ Precategory.Hom D x (Functor.F₀ R y))
 → (nat : hom-iso-natural {L = L} {R = R} λ {x} {y} → fst $ eqv {x} {y})
 → L ⊣ R
hom-equiv→adjoints eqv nat = hom-iso→adjoints (fst eqv) (snd eqv) nat

open import Cat.Morphism
open Precategory
open Functor
module R = Functor R
module L = Functor L
module iD = Functor iD
module iC = Functor iC
module C = Precategory C
module D = Precategory D
module C' = Precategory C'
module D' = Precategory D'

is-ff-prop : {oc lc od ld : _}{C : Precategory oc lc}{D : Precategory od ld}
  -> (F : Functor C D) → is-prop (is-fully-faithful F)
is-ff-prop F = hlevel!


infixr 9 _o_
_o_ : ∀{a}{b}{c} {A : Type a} {B : A → Type b} {C : {x : A} → B x → Type c} →
      (∀ {x} (y : B x) → C y) → (g : (x : A) → B x) →
      ((x : A) → C (g x))
f o g = λ x → f (g x)


restrict : (L' F∘ iC) ≅ⁿ (iD F∘ L) → (R' F∘ iD) ≅ⁿ (iC F∘ R) → L ⊣ R
restrict comm1 comm2 = hom-equiv→adjoints f
  λ {b = b} {c = c} g h x →
   fst f (D._∘_ g (D._∘_ x (L.₁ h)))
   ≡⟨ {! !} ⟩
   C._∘_ (R.₁ g) (C._∘_ (fst f x) h) ∎
  where
  f : {x : C .Ob} {y : D .Ob} → D.Hom (L.F₀ x) y ≃ C.Hom x (R.F₀ y)
  f {c} {d} =
   D.Hom (L.F₀ c) d ≃⟨ iD.F₁ , ffID ⟩
   D'.Hom (iD.F₀ (L.F₀ c)) (iD.F₀ d) ≃⟨ iso→hom-equiv D' (isoⁿ→iso ((_ Iso⁻¹) comm1) c) (id-iso _) ⟩
   D'.Hom ((L' F∘ iC).F₀ c) (iD.F₀ d) ≃⟨ L-adjunct adj , L-adjunct-is-equiv adj ⟩
   C'.Hom (iC.F₀ c) ((R' F∘ iD).F₀ d) ≃⟨ iso→hom-equiv C' (id-iso _) (isoⁿ→iso comm2 d) ⟩
   C'.Hom (iC.F₀ c) (iC.F₀ (R.F₀ d)) ≃⟨ (iC.F₁ , ffIC) e⁻¹ ⟩
   C.Hom c (R.F₀ d) ≃∎
 
 -- {!!} ∙ {!!}
 -- {!!} ∙ {!!}

```
