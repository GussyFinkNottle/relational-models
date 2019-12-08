module du where 
  module du (A : Set) (B : Set) where 

    data fm : Set where                   -- formation
      i₀ :  A → fm                       -- introduction
      i₁ :  B → fm                       -- introduction

    ex : { C : fm → Set }→              -- elimination
         ( (a : A) → C (i₀ a) )→
         ( (b : B) → C (i₁ b) )→
         ( z : fm ) → C z
    ex c₀ _  (i₀ a) = c₀ a                -- computation 0
    ex _  c₁ (i₁ b) = c₁ b                -- computation 1

    open import bool
    open import sigma

    d : fm -> bool.fm
    d = ex (λ _ → bool.mk₀) λ _ → bool.mk₁
    {- todo .. something about eta ... -}
    dd₁ : (z : fm) -> sigma.fm bool.fm (λ x → bool.EX A B x)
    dd₁ = ex {λ _ → sigma.fm bool.fm (bool.EX A B)}
             (sigma.mk bool.mk₀) (sigma.mk bool.mk₁ ) 
    dd₂ :  sigma.fm bool.fm (λ x → bool.EX A B x) -> fm
    dd₂ =  sigma.ex bool.fm (bool.EX A B) (bool.ex i₀ i₁)
    eta : {X : (_ _ : fm)-> Set} -> ((z : fm)-> X z z) ->  
          (z : fm) -> X z (dd₂ (dd₁ z)) 
    eta r = ex (λ a → r (i₀ a)) λ b → r (i₁ b)

  module du* (A : Set) (A' : Set) (A* : A → A' → Set)
             (B : Set) (B' : Set) (B* : B → B' → Set) where
    open du A  B  public
    open du A' B' public renaming (fm to fm' ; i₀ to i₀' ; i₁ to i₁' ; ex to ex')
                         hiding (d ; dd₁ ; dd₂ ; eta)

    data fm* : fm → fm' →  Set  where
       i₀* : (a : A) → (a' : A') → (a* : A* a a') → fm* (i₀ a) (i₀' a') 
       i₁* : (b : B) → (b' : B') → (b* : B* b b') → fm* (i₁ b) (i₁' b') 

    ex* : {D :  (z : fm) → (z' : fm') → fm* z z' → Set} →
          (d₀ : (a : A) → (a' : A') → (a* : A* a a') → D (i₀ a) (i₀' a') (i₀* a a' a*)) →
          (d₁ : (b : B) → (b' : B') → (b* : B* b b') → D (i₁ b) (i₁' b') (i₁* b b' b*)) →
          (z : fm) → (z' : fm') → (z* : fm* z z') → D z z' z*
    ex* {D} d₀ _  _ _ (i₀* a a' a*) = d₀ a a' a*
    ex* {D} _  d₁ _ _ (i₁* b b' a*) = d₁ b b' a*

  module du-in-model
             (A : Set) (A : Set) (A* : A → A → Set)
             (B : Set) (B : Set) (B* : B → B → Set) where
    open du* A A A* B B B* public hiding (fm' ; i₀' ; i₁' ; ex')
    module _ (C : fm → Set)
             (C* : (z z' : fm)→ (z* : fm* z z')→ C z → C z' → Set)   -- C, in the model
             (c₀ : (a : A) → C (i₀ a))
             (c₁ : (b : B) → C (i₁ b))
             (c₀* : (a : A) → (a' : A) → (a* : A* a a')→
                   C* (i₀ a) (i₀ a') (i₀* a a' a*) (c₀ a) (c₀ a')
             )
             (c₁* : (b : B) →  (b' : B) → (b* : B* b b') → 
                   C* (i₁ b) (i₁ b') (i₁* b b' b*) (c₁ b) (c₁ b')
             ) 
          where
            h : (z : fm) → C z
            h = ex {C} c₀ c₁
            D : (z : fm) → (z' : fm) → fm* z z' → Set
            D z z' z* = C* z z' z* (h z) (h z')      
            d₀ : (a a' : A) (a* : A* a a') →
                   C* (i₀ a) (i₀ a') (i₀* a a' a*) (c₀ a) (c₀ a')
            d₀ = c₀* 
            d₁ : (b b' : B) (b* : B* b b') →
                   C* (i₁ b) (i₁ b') (i₁* b b' b*) (c₁ b) (c₁ b')
            d₁ = c₁* 
            h* : (z z' : fm) → (z* : fm* z z') → D z z' z*
            h* = ex* {D} d₀ d₁


