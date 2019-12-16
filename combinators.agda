    pow : Set -> Set₁
    pow X = X -> Set

    rel : (_ _ : Set)-> Set₁
    rel X₁ X₂ = X₁ -> pow X₂

    {- We try to approach the most general type fitting the usual "haskell" defining equations -}
    
    -- combinator I 
    id : {X : Set}→ X → X
    id x = x 

    -- exchange arguments of a binary function,
    -- combinator C = (*) * (^) ^ (*)
    -- C a = (^) * a ^ (*)
    flip : {X : Set}{Y : Set}{Z : rel Y X} →
           (f : (y : Y) (x' : X) → Z y x')
           (x : X)
           (y : Y) → Z y x
    flip f x y = f y x
    
    -- combinator K
    const : {X : Set}{Y : pow X}→ (x : X) → Y x → X
    const x _ = x

    -- flip of K
    zero : {X : Set}{Y : pow X}-> (x : X)-> Y x -> Y x 
    zero _ = id 

    -- e₁ postcomposed to e₂ (ie. e₁ ∘ e₂), combinator B = (^) * (*) ^ (*)
    comp : {X : Set}{Y : Set}{Z : pow Y} → (e₁ : (y : Y) → Z y) → (e₂ : X → Y) → (x : X) → Z (e₂ x)
    comp e₁ e₂ x = e₁ (e₂ x)

    -- flip application. (Church encoding of the "1-tuple": cf "pair").
    -- power is the unit of the continuation monad.
    power : {B : Set}{E : pow B} → (b : B) → (e : (b' : B) → E b') → E b
    power b e = e b

    -- pairing combinator, (,). Extension of power to binary functions.
    -- pair = (*) * (*) * (^) ^ (*)
    pair : {A : Set}-> {B : pow A}-> {C : (a : A) -> pow (B a)}->
           (a : A)-> (b : B a) -> (c : (a' : A)-> (b' : B a')-> C a' b') -> C a b
    pair a b c = c a b
    -- flip of pairing (,)^(~)
    pair~ : {A : Set}-> {B : Set}-> {C : rel B A}->
           (a : A)-> (b : B) -> (c : (b' : B)-> (a' : A)-> C b a) -> C b a
    pair~ a b c = c b a

    private Cont : (_ _ : Set) -> Set
            Cont r a = (a -> r) -> r
    private join : {r a : Set}-> Cont r (Cont r a) -> Cont r a
            join = flip (comp power power)                           -- ((^) * (^)) ^ (~) in AMEN
    private map : {r a b : Set}-> (a -> b) -> Cont r a -> Cont r b  
            map  = comp (flip comp) (flip comp)                      -- (*) * (*) in AMEN notation

    -- e₁ precomposed to e₂. (flip comp)
    times : {X : Set}{Y : Set}{ Z : pow Y} -> 
            (f : X → Y) →
            (g : (y : Y) → Z y) → (x : X) → Z (f x)
    times e₁ e₂ b = power (power b e₁) e₂

    -- pointwise lifted times
    plus :  {B : Set}{X : pow B}{Y : pow B} -> 
           (e₁ : (b : B) → X b → Y b)
           → {Z : B -> Set} ->
             (e₂ : (b : B) → Y b → Z b) →
             (b : B) → X b → Z b
    plus e₁ e₂ b  = times (power b e₁) (power b e₂)


    -- combinator W
    -- W = flip ((^) + (^))
    diag : {X : Set}-> {Y : rel X X} ->
           (f : (x₁ x₂ : X) -> Y x₁ x₂ ) -> (x : X) -> Y x x
    diag f x = f x x 

    -- flip of W. (diag~ x = (x , x) where (,) is the pairing combinator.) 
    diag~ : {X : Set}{Y : rel X X}-> (x : X)-> (f : (x₁ x₂ : X)-> Y x₁ x₂)-> Y x x 
    diag~ x f = f x x

