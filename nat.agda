module _ where
  {- a few combinators I like -}
  pow : Set -> Set₁
  pow A = A -> Set

  rel : Set -> Set -> Set₁
  rel A B = A -> pow B 
{-
  Diag : {A : Set}-> rel A A -> pow A
  Diag r a = r a a
-}
  id   : {X : Set} -> X -> X
  id x = x
  
  _∘_ : {X Y : Set}{Z : Y -> Set} ->
        (f : (y : Y) -> Z y) -> (g : X -> Y) -> (x : X) -> Z (g x)
  (f ∘ g) x = f (g x)

  flip _~ : {X Y : Set} {Z : X -> Y -> Set} ->
         (f : (x : X) -> (y : Y) -> Z x y)-> (y : Y) -> (x : X) -> Z x y
  flip f a b = f b a
  (f ~)  = flip f
  
  const [_] : {X : Set}{Y : X -> Set}-> (x : X) -> Y x -> X
  const x _ = x
  [_] {X} {Y} x = const {X} {Y} x
  
  module nat where

    -- standard: what we are trying to interpret
    data fm : Set where
      mk0 : fm
      mkS : fm -> fm

    ex : { C : fm -> Set }->      -- eliminator
          (c0 : C mk0) ->
          (cS : (z : fm)-> C z -> C (mkS z) )->
          (z : fm)-> C z
    ex c0 _ mk0     = c0
    ex c0 cS (mkS z) = cS z (ex c0 cS z)

    -- some examples
{- Some fine examples, including division, remainder, inter al 
   are on on pp 222-223 of 
   Kleene:  "Introduction to MetaMathematics" (1967).  
-}
    module examples where 
      zero one two three : fm
      zero = mk0
      one  = mkS zero
      two  = mkS one
      three  = mkS two

      pd : fm -> fm
      pd = ex mk0 const -- (λ z _ → z)

      sgb sg : fm -> fm
      sgb = ex (mkS mk0) λ _ _ → mk0
      sg  = ex mk0 λ _ _ → mkS mk0

      -- _~ : (fm -> fm -> fm) -> fm -> fm -> fm
      -- _~ = flip {fm}{fm}{λ _ _ → fm} 

      add add' add'' : fm -> fm -> fm
      add n = ex n (λ _ → mkS)  -- as iterated successor
      
      it : {X : Set}-> fm -> (X -> X) -> X -> X 
      it n f z = ex z (const f) n -- (λ _ ->  f) n -- no use of side-argument

      add'' m n  = it {fm} m mkS n  -- again as iterated successor
      add' m n =  ((it {fm} n mkS) ∘ (it {fm} m mkS)) mk0

      sub : fm -> fm -> fm
      sub n m = it {fm} m pd n  -- ex n (λ _ → pd)
      abs-diff : fm -> fm -> fm
      abs-diff n m = add (sub n m) ((sub ~) m n)
      
      mul mul' exp exp'  : fm -> fm -> fm
      mul m n  = it {fm} n ((add ~) m) mk0 -- as iterated addition
      mul' m n = ((it {fm} n) ∘ (it {fm} m)) mkS mk0
                 
      exp b e  = it {fm} e ((mul ~) b) (mkS mk0)   -- as iterated multiplication
      exp' b e = it {fm → fm} e (it {fm} b) mkS mk0 -- using higher types
      exp~     = exp ~

      fact : fm -> fm  -- 1,2,6,24,120,....
      fact = ex one λ z → λ x → mul x (mkS z) -- (mul~ z ∘ mkS) x

      c2 : fm -> fm    -- 0,1,3,6,10,15,.... n*(n+1)/2
      c2 = ex zero  λ z → λ x → add x (mkS z) -- (add~ z ∘ mkS) x

    open examples using (pd; add; sub)

{-
    The introduction rules for relation fm* ( which I write =
    in these comments)
    stipulate how "proofs" z* of equations z=z' can be constructed.
    There is at most one proof of any given equation. (To formalise
    this, we need to move to a higher dimension...
-}

    data fm* : rel fm fm where 
         mk0* : fm* mk0 mk0
         mkS* : (z z' : fm)-> fm* z z' -> fm* (mkS z) (mkS z') 

{-
    Given an equational proof, we can use it as a template to
    construct another proof that a suitable ternary relation holds between
    the two terms z and z' proved equal by equational proof z*. 
-}

    ex* : {D : (x : fm) -> (x' : fm) -> fm* x x' -> Set }->
          D _ _ mk0* ->
          ((z z' : fm) -> (z* : fm* z z') -> D _ _ z*  -> D _ _ (mkS* z z' z*)) ->
          (z z' : fm)-> (z* : fm* z z')-> D _ _ z*
    ex* d0 dS _ _ mk0* = d0
    ex* d0 dS _ _ (mkS* z z' z*) = dS z z' z* (ex* d0 dS z z' z*)

    -- reflexity of fm*
    refl : (a : fm) -> fm* a a      
    refl  = ex {λ z → fm* z z} mk0* (λ z → mkS* z z)

    -- symmetry of fm*
    symm : (a b : fm) -> fm* a b -> fm* b a 
    symm  = ex* {λ x x' _ → fm* x' x} mk0* (λ z z' _ → mkS* z' z)

    -- The paradigm of a function *not* defined by iteration.
    private pd* : (m n : fm)-> fm* m n -> fm* (pd m) (pd n)
            pd* = ex* mk0* λ z z' z* _ → z*
            pd** :  (m n : fm)-> fm* (mkS m) (mkS n) -> fm* m n 
            pd** m n = pd* (mkS m) (mkS n)
    -- can we prove that any pr function respects fm* ?

    -- some trivialities. 
    
    t2 : (a b : fm)-> fm*  a (mkS b) -> fm* (pd a) b
    t2        = ex {λ x → (v : fm)-> fm* x (mkS v) -> fm* (pd x) v}
                   (λ v → pd* mk0 (mkS v))
                   (λ z x v → pd* (mkS z) (mkS v) )

    -- an alternative, shorter proof (induction on a)
    t2' : (a b : fm)-> fm*  a (mkS b) -> fm* (pd a) b
    t2' a b   = ex {λ x → fm* x (mkS b) -> fm* (pd x) b}
                   (pd* mk0 (mkS b)) 
                   (λ z x  → pd* (mkS z) (mkS b) ) 
                   a  

    --even shorter proof (induction on b)
    t2'' : (a b : fm)-> fm*  a (mkS b) -> fm* (pd a) b
    t2'' a    = ex {λ x → fm* a (mkS x) -> fm* (pd a) x}
                   (pd* a (mkS mk0)) 
                   (λ z _  → pd* a (mkS (mkS z)) ) 

    -- that addition respects equality on the left (augendum)
    t3L : (a a' : fm)(a* : fm* a a') -> (b : fm)-> fm* (add a b) (add a' b)
    t3L a a' a*   = ex {λ v → fm* (add a v) (add a' v)}
                      a*
                      (λ z → mkS* (add a z) (add a' z))  

    -- that addition respects equality on the right (augens)
    t3R : (a a' : fm)(a* : fm* a a') -> (b : fm)-> fm* (add b a) (add b a')
    t3R a a' a* b = ex* {λ v v₁ v₂ → fm* (add b v) (add b v₁)}
                         (refl b)
                         (λ z z' z* → mkS* (add b z) (add b z'))
                         a a' a* 

    --that addition respects equality in both arguments
    t3 : (a a' : fm)(a* : fm* a a')(b b' : fm)(b* : fm* b b') -> fm* (add a b) (add a' b')
    t3  = ex* {\ u u' u* -> (b b' : fm)(b* : fm* b b') -> fm* (add u b) (add u' b')}
              (ex* mk0*
                   (λ z z' _ → mkS* (add mk0 z) (add mk0 z')) )
              (λ z z' z* _ → ex* (mkS* z z' z*)
                                 (λ z₁ z₂ _ → mkS* (add (mkS z) z₁) (add (mkS z') z₂) ))

    t4₀ : (a : fm)-> fm* (add a mk0) a   -- holds definitionally
    t4₀ = refl 
    t4 : (a : fm) -> fm* (add mk0 a) a   -- needs an inductive proof
    t4 = ex {λ x → fm* (add mk0 x) x} mk0* (λ z → mkS* (add mk0 z) z) 

    -- following concern moving a successor operation between
    -- the arguments of addition.
    t4' : (a b : fm)-> fm* (add (mkS a) b) (add a (mkS b)) -- (mkS (add a b))
    t4' a        = ex { λ x → fm* (add (mkS a) x) (mkS (add a x)) }
                      (mkS* a (add a mk0) (refl a))
                      (λ z → mkS* (add (mkS a) z)  (add a (mkS z)) )

    t4'' : (a b : fm)-> fm*  (mkS (add a b)) (add (mkS a) b) 
    t4'' a       = ex { λ x → fm*  (mkS (add a x)) (add (mkS a) x) }
                      (mkS* (add a mk0) a (refl a)) -- (refl (add a in0))) 
                      λ z → mkS* (add a (mkS z)) (add (mkS a) z) -- (ex (mkS a) (λ _ → mkS) z) 

    e : (n n' : fm)-> fm* n n' ->  (m : fm)->   fm* (sub m n) (sub m n') 
    e           = ex* {λ x x' _ → (m : fm)-> fm* (sub m x) (sub m x')}
                      refl
                      (λ z z' _ x m → pd* (sub m z) (sub m z') (x m)) 

    e' : (m  : fm) -> (n n' : fm)-> fm* n n' ->  fm* (sub m n) (sub m n') 
    e' m        = ex* {λ x x' _ → fm* (sub m x) (sub m x')}
                      (refl m) 
                      (λ z z' _ x → pd* (sub m z) (sub m z') x) 

    -- addition respects equality in both arguments
    add-cong : (m m' : fm)(m* : fm* m m') -> (n n' : fm)-> fm* n n' ->  fm* (add m n) (add m' n') 
    add-cong m m' m*
                    = ex* {λ x x' _ → fm* (add m x) (add m' x')}
                      m* 
                      (λ z z' _  → mkS* (add m z) (add m' z') ) 

    -- subtraction respects equality in both arguments
    s'' : (m m' : fm)(m* : fm* m m') -> (n n' : fm)-> fm* n n' ->  fm* (sub m n) (sub m' n') 
    s'' m m' m*  = ex* {λ x x' _ → fm* (sub m x) (sub m' x')}
                    m* 
                    (λ z z' _  → pd* (sub m z) (sub m' z') ) 

    -- if 0=1, then for any nat n, 0=n
    a''' : fm* mk0 (mkS mk0) -> (n : fm)-> fm* mk0 n
    a''' x = ex mk0* (λ z x₁ → add-cong mk0 z x₁ mk0 ( mkS mk0) x)

    -- if 0=1, then any nat m equals each of its successors.
    a'''' : (m : fm) -> fm* mk0(mkS mk0) -> (n : fm)-> fm* m (add m n)
    a'''' m x = ex (refl m) (λ z x₁ → add-cong m (add m z) x₁ mk0( mkS mk0) x)

    -- if 0=1, then any nat m equals each of its predecessors. 
    s'''' : (m : fm) -> fm* mk0(mkS mk0) -> (n : fm)-> fm* m (sub m n)
    s'''' m x = ex (refl m) (λ z x₁ → s'' m (sub m z) x₁ mk0( mkS mk0) x)

    -- if 0=1, then all nats are equal.
    q :  fm* mk0(mkS mk0) -> (m n : fm)-> fm* m n 
    q x   
        = let base : (n : fm) → fm* mk0 n
              base = a''' x
              step : (z : fm)
                     (h : (n : fm) → fm* z n)
                     (n : fm) → fm* (mkS z) n 
              step z h n =  add-cong z n (h n) (mkS mk0) mk0(symm mk0(mkS mk0) x)
           in
           ex base step

    -- if zero equals any successor, then it equals it's own successor
    q' : (z : fm)-> fm* mk0(mkS z)-> fm* mk0(mkS mk0) 
    q'      = let base : fm* mk0(mkS mk0) → fm* mk0(mkS mk0) 
                  base = id
                  step : (z : fm) →
                           (fm* mk0(mkS z) → fm* mk0(mkS mk0)) →
                           fm* mk0(mkS (mkS z)) → fm* mk0(mkS mk0) 
                  step = λ z h e2z →
                         let -- check 
                             _ : fm* mk0(mkS (mkS z))
                             _ = e2z
                             _ : fm* mk0(mkS z) → fm* mk0(mkS mk0)
                             _ = h
                             e1z : fm* mk0(mkS z)
                             e1z = pd* mk0(mkS (mkS z)) e2z
                          in h e1z  --  (pd* mk0(mkS (mkS z)) e2z )
               in ex base step

    -- if 0=1, then all nat's are equal
    q'' : (z : fm) -> fm* mk0(mkS z) -> (m n : fm)-> fm* m n
    q'' z x = q (q' z x)

{-  
   Transitive, Euclidean, Left Euclidean    
    https://en.wikipedia.org/wiki/Euclidean_relation 
-}

    Tr E₀ E₁ : ( _ _ _ : fm) -> Set
    Tr a b c = fm* a b -> fm* b c -> fm* a c    -- transitive 
    E₀ a b c = fm* a b -> fm* a c -> fm* b c   -- (left) euclidean
    E₁ a b c = fm* a b -> fm* c b -> fm* a c   -- right euclidean

    -- I use pattern matching for simplicity.
    -- I assume this can be compiled down into something involving
    -- only ex*, perhaps ex, and the function q''.
       -- notably pattern matching hass hidden all the case-clashes.
       
    trPM : (a b c : fm) -> Tr a b c -- "PM" for pattern-matching. 
    trPM mk0 mk0 mk0 = λ _ x₁ → x₁
    trPM (mkS z) (mkS z') (mkS z'') (mkS* z z' ab) (mkS* z' z'' bc)
     = mkS* z z'' (trPM z z' z'' ab bc)

    -- Some easy cases of transitivity
    m00* : (c : fm)   -> Tr mk0 mk0 c
    m0S* : (b c : fm) -> Tr mk0 (mkS b) c
    mS0* : (a c : fm) -> Tr (mkS a) mk0 c
    mSS0 : (a b : fm) -> Tr (mkS a) (mkS b) mk0

    m00* c    = λ _ -> id
    m0S* b c  = λ x _ → q'' b x mk0 c
    mS0* a c  = λ x _ → q'' a (symm (mkS a) mk0 x) (mkS a) c
    mSS0 a b  = λ _ x₁ → q'' b (symm (mkS b) mk0 x₁) (mkS a) mk0

    -- Proof of the euclidean property. I trust that both E₁ and Tr 
    -- have proofs with roughly the same structure.
    e₀ : (a b c : fm) -> E₀ a b c  -- A painfully written replacement for pattern matching 
    e₀ =  let base : (b c : fm) → E₀ mk0 b c
              base = let ba : (c : fm) → E₀ mk0 mk0 c
                         ba = ex (λ _ → id ) λ z x x₁ x₂ → x₂
                         st : (z : fm) → ((c : fm) → E₀ mk0 z c) → (c : fm) → E₀ mk0(mkS z) c
                         st = λ z h c x₁ x₂ → q'' z x₁ (mkS z) c     {- clash -}
                      in ex ba st
              step : (z : fm) → ((b c : fm) → E₀ z b c) → (b c : fm) → E₀ (mkS z) b c
              step z h = let stba : (c : fm) (x : fm* (mkS z) mk0) (x₁ : fm* (mkS z) c) → fm* mk0 c
                             stba c x _ = q'' z (symm (mkS z) mk0 x) mk0 c     {- clash -}
                             stst : (z₁ : fm) →
                                      ((c : fm) → E₀ (mkS z) z₁ c) → (c : fm) → E₀ (mkS z) (mkS z₁) c
                             stst z₁ h₁ = let ststst : (z₂ : fm) → E₀ (mkS z) (mkS z₁) z₂ → E₀ (mkS z) (mkS z₁) (mkS z₂)
                                              ststst z₂ e h1 h2 = mkS* z₁ z₂ (h z₁ z₂ (pd* (mkS z) (mkS z₁) h1) (pd* (mkS z) (mkS z₂) h2))
                                          in ex (λ x x₁ → q'' z (symm (mkS _) mk0 x₁) (mkS z₁) mk0)   {- clash -}
                                                ststst
                          in ex stba stst 
           in ex {λ x → (b c : fm) -> E₀ x b c} base step

    -- but we have symm, so it's easy.
    e₁ : (a b c : fm) -> E₁ a b c
    e₁ a b c = λ x x₁ → e₀ b a c (symm a b x) (symm c b x₁)
    
    tr  : (a b c : fm) -> Tr a b c
    tr a b c  = λ x → e₀ b a c (symm a b x) 

{-  Very unlikely to hold, unless X respects equality.
    transport : {X : (_ _ : fm) -> Set} -> (r : (a : fm)-> X a a) -> (a b : fm)-> fm* a b -> X a b
    transport {X} r a b ab
                            = let
                                  H x x' _ = (n : fm) -> X (add x n) (add x' n)
                                  base : (b₁ : fm) → X (add mk0b₁) (add mk0b₁)
                                  base b₁ = r (add mk0b₁)
                                  step : (z z' : fm) (z* : fm* z z') →
                                        ((b₁ : fm) → X (add z b₁) (add z' b₁)) →
                                        (b₁ : fm) → X (add (mkS z) b₁) (add (mkS z') b₁)
                                  step z z' z* h = ex (h (mkS mk0)) λ z₁ h₁ → {!!} -- h (mkS {!b!}) -- h (mkS {!!}) {!!}
                               in 
                           ex* {H} -- {λ x x' x* → (b : fm) -> X (add x b) (add x' b)}
                               base 
                               step 
                               a b ab mk0
-}

{-
Translation of tt (with nat) into tt++ (with nat*)

In an empty context, sets A are translated to relations A* : rel A A
elements a are translated to proofs a* : A* a a in tt++.
 
Things are more complicated in a non-empty context. 
A tt context  (γ : Γ, x : Aγ)  (γ is the tuple of variables in Γ)
is translated by
    ( (γ,γ',γ*) : Gamma*, x : Aγ, x' : Aγ', x* : A* (γ,γ',γ*)(x,x') )
-}

{-
What the following module is about .
The parameters of this module include the premises of the
elimination rule ex for fm, and those of the corresponding
elimination rule ex* for fm*. We have to show that the conclusion
of the latter rule can be obtained using ex*. 
-}
    module _ (C   : fm -> Set)                    -- first premise of ex
             (C*  : (z z' : fm)-> fm* z z' -> rel (C z) (C z'))   -- its interpretation
             (c0  : C mk0)                        -- second premise of ex
             (c0* : C* mk0 mk0 mk0* c0 c0)        -- interpretation
             (cS  : (z : fm) → C z → C (mkS z))   -- third premise of ex
             (cS* : (z z' : fm)(z* : fm* z z')    -- iterpretation
                    (x : C z)(x' : C z')
                      -> C* z z' z* x x'
                      -> C* (mkS z) (mkS z') (mkS* z z' z*) (cS z x) (cS z' x')
             ) 
     where
       h : (z : fm) → C z                                -- conclusion of ex
       h = ex {C} c0 cS
       D : (x : fm) -> (x' : fm) -> fm* x x' -> Set      -- induction hypothesis for ex*
       D n n' n* = C* n n' n* (h n) (h n')
       d0 : D mk0 mk0 mk0*                               -- base of ex*
       d0 = c0*
       dS : (z z' : fm)(z* : fm* z z') -> D z z' z*      -- step of ex*
            -> D (mkS z) (mkS z') (mkS* z z' z*)
       dS z z' z* = cS* z z' z* (h z) (h z')  
       h* : (z z' : fm) -> (z* : fm* z z') → D z z' z*   -- interpretation of conclusion 
       h* = ex* {D} d0 dS
