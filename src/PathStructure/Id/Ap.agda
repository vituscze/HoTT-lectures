{-# OPTIONS --without-K #-}
open import Equivalence

module PathStructure.Id.Ap {a b} {A : Set a} {B : Set b}
  (f : A → B) (qi : qinv f) where

open import Functoriality
open import GrupoidStructure
open import Homotopy
open import PathOperations
open import Types

private
  g = π₁ qi
  α = π₁ (π₂ qi)
  β = π₂ (π₂ qi)

split-path : {a a′ : A} → a ≡ a′ → f a ≡ f a′
split-path = ap f

merge-path : {a a′ : A} → f a ≡ f a′ → a ≡ a′
merge-path p = β _ ⁻¹ · ap g p · β _

F : (b b′ : B) (p : b ≡ b′) →  Set
F b b′ p =
    ap f (β (g b) ⁻¹ · ap g (ap (f ∘ g) p) · β (g b′))
  ≡ ap (f ∘ g) p

F-lemma : ∀ b → F b b refl
F-lemma b = ap (ap f)
    ( ap (λ y → β (g b) ⁻¹ · y)
       (id·p (β (g b)))
    · p⁻¹·p (β (g b))
    )

ap-β-lem : ∀ a → ap (g ∘ f) (β a) ≡ β (g (f a))
ap-β-lem a
  = p·id (ap (g ∘ f) (β a)) ⁻¹
  · ap (λ y → ap (g ∘ f) (β a) · y) (p·p⁻¹ (β a) ⁻¹)
  · p·q·r (ap (g ∘ f) (β a)) (β a) (β a ⁻¹)
  · ap (λ y → y · β a ⁻¹) (naturality _ _ β (β a) ⁻¹)
  · ap (λ y → (β (g (f a)) · y) · β a ⁻¹) (ap-id (β a))
  · p·q·r (β (g (f a))) (β a) (β a ⁻¹) ⁻¹
  · ap (λ y → β (g (f a)) · y) (p·p⁻¹ (β a))
  · p·id (β (g (f a)))

add-right : ∀ {a} {A : Set a} {a₁ a₂ a₃ : B} (p q : a₁ ≡ a₂) (r : a₂ ≡ a₃) →
  (p ≡ q) ≡ (p · r ≡ q · r)
add-right {a₁ = a₁} p q r = J
  (λ a₂ _ r → (p q : a₁ ≡ a₂) → (p ≡ q) ≡ (p · r ≡ q · r))
  (λ _ p q →
    tr    (λ x → (p ≡ q) ≡ (p · refl ≡ x)) (p·id q ⁻¹)
      (tr (λ x → (p ≡ q) ≡ (x        ≡ q)) (p·id p ⁻¹) refl))
  _ _ r p q

add-left : ∀ {a} {A : Set a} {a₁ a₂ a₃ : B} (p q : a₂ ≡ a₃) (r : a₁ ≡ a₂) →
  (p ≡ q) ≡ (r · p ≡ r · q)
add-left {a₃ = a₃} p q r = J
  (λ _ a₂ r → (p q : a₂ ≡ a₃) → (p ≡ q) ≡ (r · p ≡ r · q))
  (λ _ p q →
    tr    (λ x → (p ≡ q) ≡ (refl · p ≡ x)) (id·p q ⁻¹)
      (tr (λ x → (p ≡ q) ≡ (x        ≡ q)) (id·p p ⁻¹) refl))
  _ _ r p q

ap-right : ∀ {a} {A : Set a} {a a′ : A} (p q r : a ≡ a′) →
  q ≡ r → (p ≡ q) ≡ (p ≡ r)
ap-right p q r qr = J
  (λ q r _ → (p ≡ q) ≡ (p ≡ r))
  (λ _ → refl) _ _ qr

ap-left : ∀ {a} {A : Set a} {a a′ : A} (p q r : a ≡ a′) →
  p ≡ r → (p ≡ q) ≡ (r ≡ q)
ap-left p q r pr = J
  (λ p r _ → (p ≡ q) ≡ (r ≡ q))
  (λ _ → refl) _ _ pr

F-tr : ∀ a a′ (q : f a ≡ f a′) →
  F (f a) (f a′) q ≡ (ap f (β a ⁻¹ · ap g q · β a′) ≡ q)
F-tr a a′ q =
 ( add-left  {A = A}
   (ap f (β a ⁻¹ · ap g q · β a′)) q (α (f a))
 · add-right {A = A}
   (α (f a) · ap f (β a ⁻¹ · ap g q · β a′)) (α (f a) · q) (α (f a′) ⁻¹)
 · ap-right
   ((α (f a) · ap f (β a ⁻¹ · ap g q · β a′)) · α (f a′) ⁻¹)
   ((α (f a) · q) · α (f a′) ⁻¹)
   (ap (f ∘ g) q)
   ( ap (λ y → (α (f a) · y) · α (f a′) ⁻¹) (ap-id q ⁻¹)
   · ap (λ y → y · α (f a′) ⁻¹) (naturality _ _ α q)
   · p·q·r (ap (f ∘ g) q) (α (f a′)) (α (f a′) ⁻¹) ⁻¹
   · ap (λ y → ap (f ∘ g) q · y) (p·p⁻¹ (α (f a′)))
   · p·id (ap (f ∘ g) q)
   )
 · ap-left
   ((α (f a) · ap f (β a ⁻¹ · ap g q · β a′)) · α (f a′) ⁻¹)
   (ap (f ∘ g) q)
   (ap f (β (g (f a)) ⁻¹ · ap g (ap (f ∘ g) q) · β (g (f a′))))
   ( ap (λ y → (α (f a) · y) · α (f a′) ⁻¹) (ap-id _ ⁻¹)
   · ap (λ y → y · α (f a′) ⁻¹)
     (naturality _ _ α (ap f (β a ⁻¹ · ap g q · β a′)))
   · p·q·r (ap (f ∘ g) (ap f (β a ⁻¹ · ap g q · β a′)))
     (α (f a′)) (α (f a′) ⁻¹) ⁻¹
   · ap (λ y → ap (f ∘ g) (ap f (β a ⁻¹ · ap g q · β a′)) · y)
     (p·p⁻¹ (α (f a′)))
   · p·id (ap (f ∘ g) (ap f (β a ⁻¹ · ap g q · β a′)))
   · ap-∘ f g (ap f (β a ⁻¹ · ap g q · β a′))
   · ap (ap f)
     ( ap-∘ g f (β a ⁻¹ · ap g q · β a′) ⁻¹
     · ap· (g ∘ f) (β a ⁻¹) (ap g q · β a′)
     · ap (λ y → ap (g ∘ f) (β a ⁻¹) · y)
       (ap· (g ∘ f) (ap g q) (β a′))
     · ap (λ y → y · ap (g ∘ f) (ap g q) · ap (g ∘ f) (β a′))
       (ap⁻¹ (g ∘ f) (β a))
     · ap (λ y → y ⁻¹ · ap (g ∘ f) (ap g q) · ap (g ∘ f) (β a′))
       (ap-β-lem a)
     · ap (λ y → β (g (f a)) ⁻¹ · ap (g ∘ f) (ap g q) · y)
       (ap-β-lem a′)
     · ap (λ y → β (g (f a)) ⁻¹ · y · β (g (f a′)))
       ( ap-∘ g f (ap g q)
       · ap (ap g) (ap-∘ f g q ⁻¹)
       )
     )
   )
 ) ⁻¹

proof-F : {a a′ : A} → split-path ∘ merge-path {a} {a′} ∼ id
proof-F p = tr id (F-tr _ _ p) (J F F-lemma _ _ p)

-- Copied from HoTT book, theorem 2.11.1.
proof-direct : {a a′ : A} → split-path ∘ merge-path {a} {a′} ∼ id
proof-direct {a} {a′} p
  = ap (ap f)
    (p·q·r (β a ⁻¹) (ap g p) (β a′))
  · id·p (ap f ((β a ⁻¹ · ap g p) · β a′)) ⁻¹
  · ap (λ y → y · ap f ((β a ⁻¹ · ap g p) · β a′))
    (p⁻¹·p (α (f a)) ⁻¹)
  · p·q·r (α (f a) ⁻¹) (α (f a)) (ap f ((β a ⁻¹ · ap g p) · β a′)) ⁻¹
  · ap (λ y → α (f a) ⁻¹ · α (f a) · y)
    (ap-id (ap f ((β a ⁻¹ · ap g p) · β a′)) ⁻¹)
  · ap (λ y → α (f a) ⁻¹ · y)
    (naturality _ _ α (ap f ((β a ⁻¹ · ap g p) · β a′)))
  · ap (λ y → α (f a) ⁻¹ · y · α (f a′))
    ( ap-∘ f g (ap f ((β a ⁻¹ · ap g p) · β a′))
    · ap (ap f)
      ( ap-∘ g f ((β a ⁻¹ · ap g p) · β a′) ⁻¹
      · p·id (ap (g ∘ f) ((β a ⁻¹ · ap g p) · β a′)) ⁻¹
      · ap (λ y → ap (g ∘ f) ((β a ⁻¹ · ap g p) · β a′) · y)
        (p·p⁻¹ (β a′) ⁻¹)
      · p·q·r (ap (g ∘ f) ((β a ⁻¹ · ap g p) · β a′)) (β a′) (β a′ ⁻¹)
      · ap (λ y → y · β a′ ⁻¹)
        ( naturality _ _ β ((β a ⁻¹ · ap g p) · β a′) ⁻¹
        · ap (λ y → β a · y)
          (ap-id ((β a ⁻¹ · ap g p) · β a′))
        )
      · ap (λ y → y · β a′ ⁻¹)
        (p·q·r (β a) (β a ⁻¹ · ap g p) (β a′))
      · p·q·r (β a · β a ⁻¹ · ap g p) (β a′) (β a′ ⁻¹) ⁻¹
      · ap (λ y → (β a · β a ⁻¹ · ap g p) · y)
        (p·p⁻¹ (β a′))
      · p·id (β a · β a ⁻¹ · ap g p)
      · p·q·r (β a) (β a ⁻¹) (ap g p)
      · ap (λ y → y · ap g p)
        (p·p⁻¹ (β a))
      · id·p (ap g p)
      )
    · ap-∘ f g p ⁻¹
    )
  · ap (λ y → α (f a) ⁻¹ · y)
    (naturality _ _ α p ⁻¹)
  · p·q·r (α (f a) ⁻¹) (α (f a)) (ap id p)
  · ap (λ y → y · ap id p)
    (p⁻¹·p (α (f a)))
  · ap-id p

split-merge-eq : {a a′ : A} → (a ≡ a′) ≃ (f a ≡ f a′)
split-merge-eq
  = split-path
  , (merge-path , proof-F)
  , (merge-path , λ p → J
      (λ _ _ p → merge-path (split-path p) ≡ p)
      (λ _ → p⁻¹·p (β _))
      _ _ p)
