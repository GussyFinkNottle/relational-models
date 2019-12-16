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
    Ex : 
         ( A -> Set) -> (B -> Set) -> fm -> Set
    Ex a b (i₀ x) = a x
    Ex a b (i₁ x) = b x

    open import bool
         renaming (fm to Two ; mk₀ to 0₂ ; mk₁ to 1₂ ; ex to elim₂)
    open import sigma 
    open sigma.fm public
    Σ : (A : Set) -> (A → Set) → Set
    Σ = sigma.fm
    σ : {A : Set}{B : A -> Set} -> (a : A) → B a → Σ A B 
    σ = sigma.mk 

    private d : fm -> Two -- bool.fm
            d = ex (λ _ → 0₂) (λ _ → 1₂)
    {- todo .. something about eta ... -}
    {- 
It is well-known that the "strong" forms of 
inductive elimination 
(with a dependent induction hypothesis) 
are sufficient to prove so-called "propositional eta",
which one can state using the uniform Id type former.
Alternatively, one can state the same thing "polymorphically",
which is to say, with Leibnitz equality.  
  
  Id A (a,b) 
    =def  {X : rel A A}-> ((a : A) -> X(a,a)) -> X(a,b)

In words, a and b are related by any reflexive relation.

Both pi and sigma support eta rules of this kind. 
I believe there is a wide-spread opinion that eta laws
(to the effect that the constructors are surjective)
make little sense for constructions like du, disjoint union.
However the below suggests that this is not the case.
There is in a strong sense an isomorphism between (A + B) and the 
type (Sigma Two (EX A B)) defined using an "large" eliminator, into Set.

Does it make any sense to consider an eta-law for something like nat??
    -}

    private T : Set
            T = Σ Two (EX A B)
    dd₁ : fm -> T -- sigma.fm bool.fm (λ x → bool.EX A B x)
    dd₂ : T ->  fm 
    dd₁ = ex {λ _ → T } -- sigma.fm bool.fm (bool.EX A B)}
             (σ 0₂) (σ 1₂) -- (sigma.mk bool.mk₀) (sigma.mk bool.mk₁ )
    -- dd₁# t = let dt = d t in σ (d t) {! ?!}
    dd₂ =  let h : (a : Two) (b : EX A B a) → fm
               h = elim₂ {λ z → EX A B z → fm} i₀ i₁
            in sigma.ex Two (EX A B) h -- (bool.ex i₀ i₁) -- reconstitute the du thing

    private d_better : fm -> Two
            d_better t = let h : T
                             h = dd₁ t
                          in sigma.pi0 Two (EX A B) h -- sigma.pi0 ? -- (dd₁ t)

    eta : {X : (_ _ : fm)-> Set} ->
          (r : (z : fm)-> X z z) ->  
          (z : fm) -> X z (dd₂ (dd₁ z))   -- dd₂ left inverse of dd₁ 
    eta {X} r = ex {λ z → X z (dd₂ (dd₁ z))}
                   (λ a → r (i₀ a))
                   (λ b → r (i₁ b))
    eta' : {X : (_ _ : T) -> Set} ->
           (r : (z : T)-> X z z) ->  
           (z : sigma.fm Two (EX A B)) -> X z (dd₁ (dd₂ z))   -- dd₂ left inverse of dd₁ 
    eta' {X} r = let
                     h1 : (b : A) → X (mk 0₂ b) (dd₁ (dd₂ (mk 0₂ b)))
                     h1 a = r (mk 0₂ a)
                     h2 : (b : B) -> X (mk 1₂ b) (dd₁ (dd₂ (mk 1₂ b)))
                     h2 b = r (mk 1₂ b) 
                     h : (a : Two) (b : EX A B a) → X (mk a b) (dd₁ (dd₂ (mk a b)))
                     h = elim₂ h1 h2
                  in sigma.ex  Two (EX A B) h

  module du* (A : Set) (A' : Set) (A* : A → A' → Set)
             (B : Set) (B' : Set) (B* : B → B' → Set) where
    open du A  B  public
    open du A' B' public renaming (Σ to Σ' ; σ to σ' ; fm to fm' ; i₀ to i₀' ; i₁ to i₁' ; ex to ex')
                         hiding (d ; dd₁ ; dd₂ ; eta ; eta' ; Ex)

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


