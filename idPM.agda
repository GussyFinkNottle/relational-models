module _ where

  {- Fred edited a confused draft by me, resulting in more-or-less this. -}

  rel : (A A' : Set) -> Set₁
  rel A A' = A -> A' -> Set
  pow : Set -> Set₁
  pow A = A -> Set

  -- Christine Paulin-Mohring style (singleton predicate). Maybe simpler.
  module idPM (A : Set) (a : A) where

    data fmPM : pow A where   inPM : fmPM a

    exPM : {C : (b : A) -> pow (fmPM b) }->
           C a inPM -> (b : A) -> (ab : fmPM b) -> C b ab
    exPM {C} c a inPM = c   -- : C a inPM

  module idPM* (A : Set) (A' : Set) (A* : rel A A')        -- NB heterogeneous
               (a : A) (a' : A') (a* : A* a a') where
    open idPM A  a  public    -- pull in introduction rules.
    open idPM A' a' public    -- pull in (')variants.
         renaming (fmPM to fmPM' ; inPM to inPM' ; exPM to exPM')

    data fmPM* : (b : A) (b' : A') (b* : A* b b') -> rel (fmPM b) (fmPM' b') where
      inPM* : fmPM* a a' a* inPM inPM'

    exPM* : { C* : (b : A) -> (b' : A') -> (b* : A* b b') ->
                   (z : fmPM b) -> (z' : fmPM' b') ->
                   (z* : fmPM* b b' b* z z')
                   -> Set
            } ->
            ( c* : C* a a' a* inPM inPM' inPM* ) ->
            ( b : A) ->      ( b' : A')          ->
            ( b* : A* b b')                      ->
            ( z : fmPM b) -> ( z' : fmPM' b')    ->
            ( z* : fmPM* b b' b* z z')           ->
            C* b b' b* z z' z*
    exPM* {C*} c* .a .a' .a* .inPM .inPM' inPM* = c*


  module idPM-in-model (A : Set)(A* : rel A A )
                       (a : A) (a' : A) (a* : A* a a')
               where
    open idPM* A A A* a a' a* public
    module _ (C : (b : A)-> fmPM b -> Set)
             (C' : (b' : A)-> fmPM' b' -> Set)  -- types of C and C' are alpha-convertible.
             (C* : (b : A)(b' : A)(b* : A* b b')
                   (z : fmPM b) (z' : fmPM' b') (z* : fmPM* b b' b* z z') ->
                   rel (C b z) (C' b' z')
             )
             (c : C a inPM )
             (c' : C' a' inPM' )
             (c* : C* a a' a* inPM inPM' inPM* c c')
      where

      ex* : (b : A)(b' : A)(b* : A* b b')
            (z : fmPM b) (z' : fmPM' b')(z* : fmPM* b b' b* z z') ->
            C* b b' b* z z' z* (exPM {C} c b z) (exPM' {C'} c' b' z')
      ex* b b' b* z z' z* = exPM* {D} c* b b' b* z z' z*
        where
          D : (x : A)(x' : A)(x* : A* x x') ->
              (u : fmPM x)(u' : fmPM' x') ->
              fmPM* x x' x* u u' -> Set
          D x x' x* u u' u*
            = C* x x' x* u u' u* (exPM {C} c x u) (exPM' {C'} c' x' u')
-- a⁼
-- a⁻
-- a⁺
