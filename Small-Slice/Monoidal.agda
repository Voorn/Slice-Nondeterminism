module Small-Slice.Monoidal where

-- standard library
open import Data.Unit
open import Data.Empty
open import Data.Sum
open import Data.Nat
open import Data.Product
open import Relation.Binary.PropositionalEquality

-- local
open import Small-Slice.Univ
open import Small-Slice.ND-functions
open import Small-Slice.Substructure
open import Small-Slice.Cartesian


-- disjoint union of slices
𝕌SL-⊎ : {X Y : Set} → (𝕌SL X ⊎ 𝕌SL Y) → 𝕌SL (X ⊎ Y)
𝕌SL-⊎ (inj₁ (I , f)) = I , λ i → inj₁ (f i)
𝕌SL-⊎ (inj₂ (J , g)) = J , λ j → inj₂ (g j)

𝕌SL-⊎→1 :  {X Y : Set} → {a a' : 𝕌SL X} → (𝕌SL→ X a a')
  → 𝕌SL→ (X ⊎ Y) (𝕌SL-⊎ (inj₁ a)) (𝕌SL-⊎ (inj₁ a')) 
𝕌SL-⊎→1 p i = (proj₁ (p i)) , (cong inj₁ (proj₂ (p i)))

𝕌SL-⊎→2 :  {X Y : Set} → {b b' : 𝕌SL Y} → (𝕌SL→ Y b b')
  → 𝕌SL→ (X ⊎ Y) (𝕌SL-⊎ (inj₂ b)) (𝕌SL-⊎ (inj₂ b')) 
𝕌SL-⊎→2 p i = (proj₁ (p i)) , (cong inj₂ (proj₂ (p i)))


𝕌SL-⊗-⊎ : {X Y : Set} → 𝕌SL (X × Y) → 𝕌SL (X ⊎ Y) 
𝕌SL-⊗-⊎ (I , f) = (𝕌⊎ I I) , (λ { (inj₁ i) → inj₁ (proj₁ (f i)) ;
                                  (inj₂ i) → inj₂ (proj₂ (f i))})

𝕌SL-⊗ : {X Y  : Set} → 𝕌SL X → 𝕌SL Y → 𝕌SL (X × Y)
𝕌SL-⊗ (I , f) (J , g) = (𝕌× I J) , (λ {(x , y) → (f x) , (g y)})

𝕌SL-⊗→ : {X Y : Set} → {a a' : 𝕌SL X} → (𝕌SL→ X a a') → {b b' : 𝕌SL Y} → (𝕌SL→ Y b b')
  → 𝕌SL→ (X × Y) (𝕌SL-⊗ a b) (𝕌SL-⊗ a' b') 
𝕌SL-⊗→ a⊂a' b⊂b' (i , j) = (proj₁ (a⊂a' i) , proj₁ (b⊂b' j)) ,
  cong₂ (_,_) (proj₂ (a⊂a' i)) (proj₂ (b⊂b' j))


-- Auxiliary definitions (product category)
𝕌Bihom : (A B : Set × Set) → Set
𝕌Bihom (A₀ , A₁) (B₀ , B₁) = 𝕌Hom A₀ B₀ × 𝕌Hom A₁ B₁

𝕌Bihom-∘ : {A B C : Set × Set} → 𝕌Bihom B C → 𝕌Bihom A B → 𝕌Bihom A C
𝕌Bihom-∘ g f = 𝕌Hom-∘ (proj₁ g) (proj₁ f) , 𝕌Hom-∘ (proj₂ g) (proj₂ f)

𝕌Bihom-⊂ : {A B : Set × Set} → 𝕌Bihom A B → 𝕌Bihom A B → Set
𝕌Bihom-⊂ (f , f') (g , g') = 𝕌Hom-⊂ f g × 𝕌Hom-⊂ f' g'

𝕌Bihom-≡ : {A B : Set × Set} → 𝕌Bihom A B → 𝕌Bihom A B → Set
𝕌Bihom-≡ (f , f') (g , g') = 𝕌Hom-≡ f g × 𝕌Hom-≡ f' g'


-- Bifunctor on ×
𝕌Hom-⊗ : {X X' Y Y' : Set} → (p : 𝕌Hom X X' × 𝕌Hom Y Y')
  → 𝕌Hom (X × Y) (X' × Y')
𝕌Hom-⊗ (f , g) (x , y) = 𝕌SL-⊗ (f x) (g y)

𝕌Hom-⊗-id : {X Y : Set} → 𝕌Hom-≡ (𝕌Hom-⊗ (𝕌Hom-id X , 𝕌Hom-id Y)) (𝕌Hom-id (X × Y))
𝕌Hom-⊗-id = (λ x i → tt , refl) , (λ x i → (tt , tt) , refl)

𝕌Hom-⊗-∘ : {A B C : Set × Set} → {f : 𝕌Bihom A B} → {g : 𝕌Bihom B C} 
  → 𝕌Hom-≡ (𝕌Hom-⊗ (𝕌Bihom-∘ g f) ) (𝕌Hom-∘ (𝕌Hom-⊗ g) (𝕌Hom-⊗ f))
proj₁ 𝕌Hom-⊗-∘ (x , y) ((i , j) , (i' , j')) = ((i , i') , (j , j')) , refl
proj₂ 𝕌Hom-⊗-∘ (x , y) ((i , i') , (j , j')) = ((i , j) , (i' , j')) , refl

𝕌Hom-⊗-⊂ : {A B : Set × Set} → {f g : 𝕌Bihom A B} → 𝕌Bihom-⊂ f g
  → 𝕌Hom-⊂ (𝕌Hom-⊗ f) (𝕌Hom-⊗ g)
𝕌Hom-⊗-⊂ (f₀⊂g₀ , f₁⊂g₁) (x , y) (i , j) =
  ((proj₁ (f₀⊂g₀ x i)) , (proj₁ (f₁⊂g₁ y j))) ,
  (cong₂ _,_ (proj₂ (f₀⊂g₀ x i)) (proj₂ (f₁⊂g₁ y j)))

𝕌Hom-⊗-≡ : {A B : Set × Set} → {f g : 𝕌Bihom A B} → 𝕌Bihom-≡ f g
  → 𝕌Hom-≡ (𝕌Hom-⊗ f) (𝕌Hom-⊗ g)
𝕌Hom-⊗-≡ ((f₀⊂g₀ , g₀⊂f₀) , (f₁⊂g₁ , g₁⊂f₁)) = 𝕌Hom-⊗-⊂ (f₀⊂g₀ , f₁⊂g₁) ,
  𝕌Hom-⊗-⊂ (g₀⊂f₀ , g₁⊂f₁)


-- Monoidal
-- Left-unitor
𝕌Hom-⊗-luni : {X : Set} → 𝕌Hom (⊤ × X) X
𝕌Hom-⊗-luni x = 𝕌SL-η (proj₂ x)

𝕌Hom-⊗-luni-rev : {X : Set} → 𝕌Hom X (⊤ × X)
𝕌Hom-⊗-luni-rev x = 𝕌SL-η (tt , x)

𝕌Hom-⊗-luni-liso : {X : Set}
  → 𝕌Hom-≡ (𝕌Hom-∘ 𝕌Hom-⊗-luni-rev 𝕌Hom-⊗-luni) (𝕌Hom-id (⊤ × X))
𝕌Hom-⊗-luni-liso = (λ x i → tt , refl) , (λ x i → (tt , tt) , refl)

𝕌Hom-⊗-luni-riso : {X : Set}
  → 𝕌Hom-≡ (𝕌Hom-∘ 𝕌Hom-⊗-luni 𝕌Hom-⊗-luni-rev) (𝕌Hom-id X)
𝕌Hom-⊗-luni-riso = (λ x i → tt , refl) , (λ x i → (tt , tt) , refl)


-- Right-unitor
𝕌Hom-⊗-runi : {X : Set} → 𝕌Hom (X × ⊤) X
𝕌Hom-⊗-runi x = 𝕌SL-η (proj₁ x)

𝕌Hom-⊗-runi-rev : {X : Set} → 𝕌Hom X (X × ⊤)
𝕌Hom-⊗-runi-rev x = 𝕌SL-η (x , tt)

𝕌Hom-⊗-runi-liso : {X : Set}
  → 𝕌Hom-≡ (𝕌Hom-∘ 𝕌Hom-⊗-runi-rev 𝕌Hom-⊗-runi) (𝕌Hom-id (X × ⊤))
𝕌Hom-⊗-runi-liso = (λ x i → tt , refl) , (λ x i → (tt , tt) , refl)

𝕌Hom-⊗-runi-riso : {X : Set}
  → 𝕌Hom-≡ (𝕌Hom-∘ 𝕌Hom-⊗-runi 𝕌Hom-⊗-runi-rev) (𝕌Hom-id X)
𝕌Hom-⊗-runi-riso = (λ x i → tt , refl) , (λ x i → (tt , tt) , refl)

-- Associator
𝕌Hom-⊗-asso : {X Y Z : Set} → 𝕌Hom ((X × Y) × Z) (X × (Y × Z))
𝕌Hom-⊗-asso ((x , y) , z) = 𝕌SL-η (x , (y , z))

𝕌Hom-⊗-asso-rev : {X Y Z : Set} → 𝕌Hom (X × (Y × Z)) ((X × Y) × Z)
𝕌Hom-⊗-asso-rev (x , (y , z)) = 𝕌SL-η ((x , y) , z)



-- Comonoid structure
𝕌Hom-delete : {X : Set} → 𝕌Hom X ⊤
𝕌Hom-delete x = 𝕌SL-η tt

𝕌Hom-copy : {X : Set} → 𝕌Hom X (X × X)
𝕌Hom-copy x = 𝕌SL-η (x , x)


-- Comonoid naturality conditions
𝕌Hom-delete-nat' : {X Y : Set} → (f : 𝕌Hom X Y)
  → 𝕌Hom-⊂ (𝕌Hom-∘ 𝕌Hom-delete f) 𝕌Hom-delete 
𝕌Hom-delete-nat' f x i = tt , refl

𝕌Hom-delete-nat : {X Y : Set} → (f : 𝕌Hom X Y) → (𝕌-Total f)
  → 𝕌Hom-≡ (𝕌Hom-∘ 𝕌Hom-delete f) 𝕌Hom-delete 
proj₁ (𝕌Hom-delete-nat f f-tot) = 𝕌Hom-delete-nat' f
proj₂ (𝕌Hom-delete-nat f f-tot) x tt = ((f-tot x) , tt) , refl


𝕌Hom-copy-nat' : {X Y : Set} → (f : 𝕌Hom X Y)
  → 𝕌Hom-⊂ (𝕌Hom-∘ 𝕌Hom-copy f) (𝕌Hom-∘ (𝕌Hom-⊗ (f , f)) 𝕌Hom-copy)
𝕌Hom-copy-nat' f x (i , tt) = (tt , (i , i)) , refl

𝕌Hom-copy-nat : {X Y : Set} → (f : 𝕌Hom X Y) → (𝕌-Deter f)
  → 𝕌Hom-≡ (𝕌Hom-∘ 𝕌Hom-copy f) (𝕌Hom-∘ (𝕌Hom-⊗ (f , f)) 𝕌Hom-copy)
proj₁ (𝕌Hom-copy-nat f f-det) = 𝕌Hom-copy-nat' f
proj₂ (𝕌Hom-copy-nat f f-det) x (tt , i , j) = (i , tt) ,
  (cong (λ z → proj₂ (f x) i , z) (sym (f-det x i j)))


-- product ⊎
𝕌Hom-⊎ : {X Y Z W : Set} → 𝕌Hom X Y × 𝕌Hom Z W → 𝕌Hom (X ⊎ Z) (Y ⊎ W)
𝕌Hom-⊎ (f , g) (inj₁ x) = proj₁ (f x) , λ i → inj₁ (proj₂ (f x) i)
𝕌Hom-⊎ (f , g) (inj₂ y) = proj₁ (g y) , λ j → inj₂ (proj₂ (g y) j)


𝕌Hom-⊎-id : (X Y : Set) → 𝕌Hom-≡ (𝕌Hom-⊎ (𝕌Hom-id X , 𝕌Hom-id Y)) (𝕌Hom-id (X ⊎ Y))
proj₁ (𝕌Hom-⊎-id X Y) (inj₁ x) i = (tt , refl)
proj₁ (𝕌Hom-⊎-id X Y) (inj₂ x) i = (tt , refl)
proj₂ (𝕌Hom-⊎-id X Y) (inj₁ x) i = (tt , refl)
proj₂ (𝕌Hom-⊎-id X Y) (inj₂ x) i = (tt , refl)

𝕌Hom-⊎-∘ : {A B C : Set × Set} → (f : 𝕌Bihom A B) → (g : 𝕌Bihom B C)
  → 𝕌Hom-≡ (𝕌Hom-⊎ (𝕌Bihom-∘ g f)) (𝕌Hom-∘ (𝕌Hom-⊎ g) (𝕌Hom-⊎ f))
𝕌Hom-⊎-∘ f g =
  (λ {(inj₁ x) ij → ij , refl ; (inj₂ y) ij → ij , refl}) ,
  (λ {(inj₁ x) ij → ij , refl ; (inj₂ y) ij → ij , refl})


𝕌Hom-⊎-⊂ : {A B : Set × Set} → (f g : 𝕌Bihom A B)
  → 𝕌Bihom-⊂ f g → 𝕌Hom-⊂ (𝕌Hom-⊎ f) (𝕌Hom-⊎ g)
𝕌Hom-⊎-⊂ f g (f⊂f' , g⊂g') (inj₁ x) i = proj₁ (f⊂f' x i) , cong inj₁ (proj₂ (f⊂f' x i))
𝕌Hom-⊎-⊂ f g (f⊂f' , g⊂g') (inj₂ z) j = proj₁ (g⊂g' z j) , cong inj₂ (proj₂ (g⊂g' z j))

𝕌Hom-⊎-≡ : {A B : Set × Set} → (f g : 𝕌Bihom A B)
  → 𝕌Bihom-≡ f g → 𝕌Hom-≡ (𝕌Hom-⊎ f) (𝕌Hom-⊎ g)
𝕌Hom-⊎-≡ f g ((f⊂g , g⊂f) , (f'⊂g' , g'⊂f')) =
  (𝕌Hom-⊎-⊂ f g (f⊂g , f'⊂g')) , (𝕌Hom-⊎-⊂ g f (g⊂f , g'⊂f'))


-- left unitor
𝕌Hom-⊎-luni : {X : Set} → 𝕌Hom (⊥ ⊎ X) X
𝕌Hom-⊎-luni (inj₂ x) = 𝕌SL-η x

𝕌Hom-⊎-luni-rev : {X : Set} → 𝕌Hom X (⊥ ⊎ X)
𝕌Hom-⊎-luni-rev x = 𝕌SL-η (inj₂ x)

-- right unitor
𝕌Hom-⊎-runi : {X : Set} → 𝕌Hom (X ⊎ ⊥) X
𝕌Hom-⊎-runi (inj₁ x) = 𝕌SL-η x

𝕌Hom-⊎-runi-rev : {X : Set} → 𝕌Hom X (X ⊎ ⊥)
𝕌Hom-⊎-runi-rev x = 𝕌SL-η (inj₁ x)

-- associator
𝕌Hom-⊎-asso : {X Y Z : Set} → 𝕌Hom ((X ⊎ Y) ⊎ Z) (X ⊎ (Y ⊎ Z))
𝕌Hom-⊎-asso (inj₁ (inj₁ x)) = 𝕌SL-η (inj₁ x)
𝕌Hom-⊎-asso (inj₁ (inj₂ y)) = 𝕌SL-η (inj₂ (inj₁ y))
𝕌Hom-⊎-asso (inj₂ z) = 𝕌SL-η (inj₂ (inj₂ z))

𝕌Hom-⊎-asso-rev : {X Y Z : Set} → 𝕌Hom (X ⊎ (Y ⊎ Z)) ((X ⊎ Y) ⊎ Z)
𝕌Hom-⊎-asso-rev (inj₁ x) = 𝕌SL-η (inj₁ (inj₁ x))
𝕌Hom-⊎-asso-rev (inj₂ (inj₁ y)) = 𝕌SL-η (inj₁ (inj₂ y))
𝕌Hom-⊎-asso-rev (inj₂ (inj₂ z)) = 𝕌SL-η (inj₂ z)


-- merge operation
𝕌-merge :  {X : Set} → 𝕌Hom (X ⊎ X) X
𝕌-merge {X} = 𝕌-copr-glue (𝕌Hom-id X) (𝕌Hom-id X)

𝕌-merge-prop : {X Y Z : Set} → (f : 𝕌Hom X Z) → (g : 𝕌Hom Y Z)
  → 𝕌Hom-≡ (𝕌Hom-∘ 𝕌-merge (𝕌Hom-⊎ (f , g))) (𝕌-copr-glue f g)
proj₁ (𝕌-merge-prop f g) (inj₁ x) (i , tt) = i , refl
proj₁ (𝕌-merge-prop f g) (inj₂ y) (j , tt) = j , refl
proj₂ (𝕌-merge-prop f g) (inj₁ x) i = (i , tt) , refl
proj₂ (𝕌-merge-prop f g) (inj₂ y) j = (j , tt) , refl


-- share operation
𝕌-share :  {X : Set} → 𝕌Hom X (X ⊎ X)
𝕌-share {X} = 𝕌-prod-glue (𝕌Hom-id X) (𝕌Hom-id X)

𝕌-share-prop : {X Y Z : Set} → (f : 𝕌Hom X Y) → (g : 𝕌Hom X Z)
  → 𝕌Hom-≡ (𝕌Hom-∘ (𝕌Hom-⊎ (f , g)) 𝕌-share) (𝕌-prod-glue f g)
proj₁ (𝕌-share-prop f g) x (inj₁ tt , i) = (inj₁ i) , refl
proj₁ (𝕌-share-prop f g) x (inj₂ tt , j) = (inj₂ j) , refl
proj₂ (𝕌-share-prop f g) x (inj₁ i) = (inj₁ tt , i) , refl
proj₂ (𝕌-share-prop f g) x (inj₂ j) = (inj₂ tt , j) , refl
