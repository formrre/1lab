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
{-
hom-equiv→adjoints : ∀{o ℓ o' ℓ'} {C : Precategory o ℓ}{D : Precategory o' ℓ'}
 → {L : Functor D C} {R : Functor C D}
 → (eqv : ∀{x}{y} → Precategory.Hom C (Functor.F₀ L x) y ≃ Precategory.Hom D x (Functor.F₀ R y))
 → (nat : hom-iso-natural {L = L} {R = R} λ {x} {y} → fst $ eqv {x} {y})
 → L ⊣ R
hom-equiv→adjoints eqv nat = hom-iso→adjoints (fst eqv) (snd eqv) nat

open import Cat.Morphism
open Precategory
open Functor
open import Cat.Functor.Reasoning as Func
module R = Func R
module L = Func L
module iD = Func iD
module iC = Func iC
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

{-
restrict : (L' F∘ iC) ≅ⁿ (iD F∘ L) → (R' F∘ iD) ≅ⁿ (iC F∘ R) → L ⊣ R
restrict comm1 comm2 = hom-equiv→adjoints f
  λ {b = b} {c = c} g h x →
   fst f (D._∘_ g (D._∘_ x (L.₁ h)))
   ≡⟨ {! !} ⟩
   C._∘_ (R.₁ g) (C._∘_ (fst f x) h) ∎
  where
  f : {c : C .Ob} {d : D .Ob} → D.Hom (L.F₀ c) d ≃ C.Hom c (R.F₀ d)
  f {c} {d} =
   D.Hom (L.F₀ c) d ≃⟨ iD.F₁ , ffID ⟩
   D'.Hom (iD.F₀ (L.F₀ c)) (iD.F₀ d) ≃⟨ iso→hom-equiv D' (isoⁿ→iso ((_ Iso⁻¹) comm1) c) (id-iso _) ⟩
   D'.Hom ((L' F∘ iC).F₀ c) (iD.F₀ d) ≃⟨ L-adjunct adj , L-adjunct-is-equiv adj ⟩
   C'.Hom (iC.F₀ c) ((R' F∘ iD).F₀ d) ≃⟨ iso→hom-equiv C' (id-iso _) (isoⁿ→iso comm2 d) ⟩
   C'.Hom (iC.F₀ c) (iC.F₀ (R.F₀ d)) ≃⟨ (iC.F₁ , ffIC) e⁻¹ ⟩
   C.Hom c (R.F₀ d) ≃∎
 -}
-- we go against the conventional wisdom and built the natural isomorphism directly
open import Cat.Functor.Hom
-- hom-iso'→adjoints : (∀{x} {y} → let w = {!!} ≅ⁿ {!!}) → L ⊣ R
-- hom-iso'→adjoints = {!!}
-}
import Cat.Reasoning as Cat
import Cat.Functor.Reasoning as Func
open import Cat.Functor.Hom
open import Cat.Instances.Product
open import Cat.Instances.Functor

module _ {z ℓ o'} {C : Precategory z ℓ} {D : Precategory o' ℓ}
         {L : Functor D C} {R : Functor C D}
         where
  private
    module C = Cat C
    module D = Cat D
    module L = Func L
    module R = Func R

  hom-natural-iso→adjoints'
    : (Hom[-,-] C F∘ (Functor.op L F× Id)) ≅ⁿ (Hom[-,-] D F∘ (Id F× R))
    → L ⊣ R
  hom-natural-iso→adjoints' eta =
    hom-iso→adjoints (to .η _) (natural-iso-to-is-equiv eta (_ , _)) λ g h x →
      happly (to .is-natural _ _ (h , g)) x
    where
      open Isoⁿ eta
      open _=>_


module _ {z ℓ o' ℓ'} {C : Precategory z ℓ} {D : Precategory o' ℓ'}
         {L : Functor D C} {R : Functor C D}
         where
  private
    module C = Cat C
    module D = Cat D
    module L = Func L
    module R = Func R

  Lift-Sets : {ℓ ℓ' : _} → Functor (Sets ℓ) (Sets (ℓ ⊔ ℓ'))
  Lift-Sets {ℓ' = ℓ'} .Functor.F₀ x = el (Lift ℓ' (n-Type.∣_∣ x)) hlevel!
  Lift-Sets .Functor.F₁ x (lift lower) = lift (x lower)
  Lift-Sets .Functor.F-id = refl
  Lift-Sets .Functor.F-∘ _ _ = refl
  
  hom-natural-iso→adjoints''
    :
     (let lh = Hom[-,-] C F∘ (Functor.op L F× Id) in
      let rh = Hom[-,-] D F∘ (Id F× R) in
      Lift-Sets {ℓ' = ℓ'} F∘ lh ≅ⁿ (Lift-Sets {ℓ' = ℓ} F∘ rh))
     -- 
     -- in let r = (Hom[-,-] D F∘ (Id F× R) in ?)
    → L ⊣ R
  -- hom-natural-iso→adjoints''
  -- hom-natural-iso→adjoints'' record { to = to ; from = from ; inverses = inverses } =
  hom-natural-iso→adjoints'' ni@(record { to = to ; from = from ; inverses = record { invl = invl ; invr = invr } }) =
    hom-iso→adjoints (λ x → Lift.lower (_=>_.η to _ (lift x)))
      (λ {x = x} {y = y} → is-iso→is-equiv
       (iso (λ w → Lift.lower (_=>_.η from _ (lift w)))
            (λ w →
             Lift.lower (_=>_.η to (x , y) (lift (Lift.lower (_=>_.η from (x , y) (lift w)))))
              ≡⟨⟩
             Lift.lower (_=>_.η to (x , y) (_=>_.η from (x , y) (lift w)))
              ≡⟨
               ( let m = happly (ap _=>_.η invl) (x , y) in let q = happly m (lift w) in ap Lift.lower q )
               ⟩
         
             w ∎
             )
            λ w →
              Lift.lower (_=>_.η from (x , y) (_=>_.η to (x , y) (lift w)))
               ≡⟨ (let m = happly (ap _=>_.η invr) (x , y) in let q = happly m (lift w) in ap Lift.lower q) ⟩
              w ∎)
       )
     -- (record { is-eqv = λ y → let w = _=>_.η from {!!} in contr {!x!} , {!!}) {!!} })
     λ {b = b} {c = cu} {d = du} g h x → let z = to .is-natural _ (cu , b) (h , g) in
        ap Lift.lower (happly z (lift x))
         where
           open _=>_
open Precategory
module D = Cat D
module L = Func L
module C = Cat C
module R = Func R
module iC = Func iC
module iD = Func iD
module C' = Cat C'
module D' = Cat D'
open import Cat.Morphism
open Functor
restrict-NI : (L' F∘ iC) ≅ⁿ (iD F∘ L) → (R' F∘ iD) ≅ⁿ (iC F∘ R) → L ⊣ R
restrict-NI comm1 comm2 = hom-natural-iso→adjoints'' let f = f in {!!}
  where
  f : {c : C .Ob} {d : D .Ob} → D.Hom (L.F₀ c) d ≃ C.Hom c (R.F₀ d)
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
