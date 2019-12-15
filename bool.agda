-- module _ where

  module bool where

    data fm : Set where
      mk₀ mk₁ : fm 

    ex : { C : fm -> Set }->      -- eliminator
         (C mk₀)-> (C mk₁)->
         (z : fm)-> C z
    ex c _ mk₀ = c
    ex _ c mk₁ = c

    not : fm -> fm
    or and exp eq nor nand xor : fm -> fm -> fm
    and      = ex mk₀ 
    exp      = ex mk₁
    not      = exp mk₀ 
    or z     = ex z mk₁  
    nor z    = ex (not z) mk₀  
    nand z   = ex mk₁ (not z)
    xor z    = ex z (not z)
    eq z     = ex (not z) z    -- and (exp z z') (exp z' z)

    EX : ( _ _ : Set) -> fm -> Set
    EX A _ mk₀ = A
    EX _ B mk₁ = B

    data fm* : fm -> fm -> Set where
      mk₀* : fm* mk₀ mk₀
      mk₁* : fm* mk₁ mk₁

    ex* : { D : (x : fm) -> (x' : fm) -> fm* x x' -> Set }->
          D mk₀ mk₀ mk₀* -> D mk₁ mk₁ mk₁* ->
          (z z' : fm)-> (z* : fm* z z')-> D z z' z*
    ex* d₀ _  _ _ mk₀* = d₀
    ex* _  d₁ _ _ mk₁* = d₁

    flip : fm -> fm
    flip = ex mk₁ mk₀
    id : fm -> fm
    id = ex mk₀ mk₁ 

    {- show it is an equivalence relation -}
    refl : (z : fm )-> fm* z z
    symm : (z z' : fm)-> fm* z z' -> fm* z' z

    refl  = ex {λ z → fm* z z} mk₀* mk₁* 
    symm  = ex* {λ x x' _ → fm* x' x} mk₀* mk₁*
    {- for the following, see http://www.cse.chalmers.se/~coquand/setoid.pdf
       page 1, "We express also that it is symmetric and transitive in a way
       similar to Kan extensions ...". 
    -}
    -- if two paths have a common origin, there is a path between their destinations
    euclid : (a b : fm) -> fm* a b -> (c : fm)-> fm* a c -> fm* b c 
    euclid = ex* {λ x x' _ → (y : fm)-> fm* x y -> fm* x' y } (λ y x → x)  (λ y x → x) 
    -- if two paths have a common destination, there is a path between their origins
    left-euclid : (a b : fm) -> fm* a b -> (c : fm)-> fm* c b -> fm* c a 
    left-euclid = ex* {λ x x' _ → (y : fm)-> fm* y x' -> fm* y x } (λ y x → x) (λ y x → x) 
    -- transitivity
    trans : (a b : fm) -> fm* a b -> (c : fm)-> fm* b c -> fm* a c 
    trans = ex* {λ x x' _ → (y : fm)-> fm* x' y -> fm* x y } (λ y x → x) (λ y x → x) 

    -- actually, given symm, the last three lemmas are equivalent.

    module _
          (C : fm -> Set)
          (C* : (z z' : fm)-> fm* z z' -> C z -> C z' -> Set)
          (c₀ : C mk₀) (c₁ : C mk₁)
          (c₀* : C* mk₀ mk₀ mk₀* c₀ c₀) 
          (c₁* : C* mk₁ mk₁ mk₁* c₁ c₁) where 
      h : (z : fm) -> C z
      h = ex c₀ c₁
      D :  (x : fm) -> (x' : fm) -> fm* x x' -> Set
      D x x' x* = C* x x' x* (h x) (h x')
      d₀ : D mk₀ mk₀ mk₀* 
      d₀ = c₀*
      d₁ : D mk₁ mk₁ mk₁* 
      d₁ = c₁*
      h* : (z z' : fm)-> (z* : fm* z z')-> D z z' z*
      h* = ex* {D} d₀ d₁

    module furtling where
      {-
      Some furtling to do with proving 0=1.
      Arising out the question to what extent can we 
      accomplish what we can accomplish with general eqf
      and/or general transport.
      A paper of Jan Smith's comes to mind...
      https://www.projecteuclid.org/euclid.jsl/1183742723 
      It shows that in type-theory without a universe, 
      there is no way to prove Peano's 4th axiom 0 ̸= 1.
      -}
      EX* : fm* mk₀ mk₁ -> Set   
      EX* ()                             -- large elimination
      EXX* : (z : fm* mk₀ mk₁) -> EX* z  -- small elimination
      EXX* ()
      
      EXX01* : (C : Set) -> (z* : fm* mk₀ mk₁)-> C
      EXX10* : (C : Set) -> (z* : fm* mk₁ mk₀)-> C
      EXX01* C () 
      EXX10* C ()

      module microscopic where
      
        data N₀ : Set where
        ex₀ : { X : N₀ -> Set }-> (z : N₀)-> X z
        ex₀ () 
        T₀ : N₀ -> Set
        T₀ ()
        thing : (z : N₀) → T₀ z
        thing = ex₀ {T₀}
        
        data N₁ : Set where ⋆ : N₁
        ex₁ : { X : N₁ -> Set } -> (z : N₁)-> X ⋆ ->  X z
--        ex₁ _ x⋆ = x⋆ 
        ex₁ ⋆ x⋆ = x⋆ 
        T₁ : N₁ -> Set
        T₁ ⋆ = N₀
        thing₁ : (z : N₁) →  T₁ ⋆ ->   T₁ z 
        thing₁ = ex₁ {T₁}  
        
        N₂ : Set        -- universe closed under pi, sigma, identity,.. 
        N₂ = fm
        T₂ : N₂ -> Set
        T₂ mk₀ = N₀
        T₂ mk₁ = N₁

        eqb : (_ _ : fm)-> fm   -- returns mk₁ if arguments equal
        eqb n = ex (flip n) (id n)
        EQ₂ : (_ _ : fm)-> Set
        EQ₂ m n = T₂ (eqb m n)
        transport : (C : fm -> Set)-> (m n : fm)-> EQ₂ m n -> C m -> C n
        transport C 
                         = let
                               zero : {X : Set}-> {Y : X -> Set}-> (x : X) -> Y x → Y x
                               zero _ y = y

                               l00 : EQ₂ mk₀ mk₀ → C mk₀ → C mk₀ 
                               l00 = zero --  ex₁ also works
                               l01 : EQ₂ mk₀ mk₁ → C mk₀ → C mk₁ 
                               l01 = ex₀ 
                               l10 : EQ₂ mk₁ mk₀ → C mk₁ → C mk₀
                               l10 = ex₀ 
                               l11 : EQ₂ mk₁ mk₁ → C mk₁ → C mk₁ 
                               l11 = zero --  ex₁ also works 
                               
                               b₀  : (z : fm) → EQ₂ mk₀ z → C mk₀ → C z 
                               b₀ = ex l00 l01
                               b₁  : (z : fm) → EQ₂ mk₁ z → C mk₁ → C z 
                               b₁ = ex l10 l11
                               qed  : (z : fm) → (n : fm) → EQ₂ z n → C z → C n
                               qed = ex b₀ b₁ -- ex b₀' b₁' 
                            in ex {λ x → (n : fm) → EQ₂ x n → C x → C n}
                                   b₀ b₁  
                            
