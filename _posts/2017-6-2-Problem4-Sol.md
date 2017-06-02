---
layout: post
title: "Problem #4 Solution"
---

*[Problem #4 is here](https://coq-math-problems.github.io/Problem4/)*

*[Problem #4 Solution File](https://github.com/Coq-Math-Problems/Problems/blob/master/P4/P4_solution.v)*

**Preliminaries**

Two important lemmas we will need are the type-theoretic axiom of choice and decidable equality for `Fin`.

The axiom of choice is expressed as

` Definition AC{X Y}(P : X -> Y -> Prop) :
  (forall x, {y : Y & P x y}) -> {f : X -> Y & forall x, P x (f x)} `
  
and allows us to construct functions satisfying certain properties from constructive proofs.

Decidable equality is expressed as

` Lemma Fin_dec_eq : forall (n : nat)(i j : Fin n), {i = j} + {i <> j} `

and will allow us to define functions on `Fin n` in a more 'pointwise' fashion.

**Injection to surjection**

The main argument uses an induction on `n`.  The zero case trivial.  If `f : Fin (S n) -> Fin (S n)` is an injection, our goal will be to somehow construct a related injection `fhat : Fin n -> Fin n` which will allow us to use the inductive hypothesis in a useful manner.

The easiest case to consider is when `f (inl tt) = inl tt`, since we can prove using injectivity that for any `x` `f (inr x) = inr y` for some `y`; then, using `AC`, we could create a function `fhat : Fin n -> Fin n` which related each such `x` to `y` which is obviously injective.  By the inductive hypothesis, `fhat` is a surjection, so we can then easily show from there that `f` is surjective.

Of course, we can't make this assumption, but we can slightly modify `f` so this is the case:  just switch `f (inl tt)` and `inl tt` in `f`.  Since `Fin (S n)` has decidable equality, we can do this by composing `f` with a transposition function:

    Definition transpose(n : nat)(i j : Fin n) : Fin n -> Fin n :=
      fun x => match Fin_dec_eq n i x with
               |left  _ => j
               |right _ => match Fin_dec_eq n j x with
                           |left  _ => i
                           |right _ => x
                           end
               end.

**Surjection to injection**

We will prove and use a lemma which says that `Fin n` cannot surjection onto `Fin (S n)`:

` Lemma no_surj_n_Sn : forall (n : nat)(f : Fin n -> Fin (S n)), surj f -> False.`

Once more, we induct on `n`, and the zero case is trivial.  Suppose then that we have a surjection `f : Fin (S n) -> Fin (S (S n))`.  We have two cases to consider:

*Case i* `f (inl tt) = inl tt`

In this case, we know from surjectivity of `f` that every `inr y` is hit by some `inr x`.  Thus, we have a surjection `Fin n -> Fin (S n)`, a contradiction.

*Case ii* `f (inl tt) = inr y0`

In this case, we can't show that every `inr y` is hit by an `inr x`, since `inl tt` might be the only element to hit `inr y0`.  However, we know that there is some `inr x` that hits `inl tt`, and we can just redirect that one element to `y0`.  Again, we can then produce the desired surjection `Fin n -> Fin (S n)`.

With this lemma in hand, we are ready to prove the main result.  Again, the zero is case is easy. Suppose `f : Fin (S n) -> Fin (S n)` is a surjection and suppose `f x = f x'`.  Since `Fin (S n)` has decidable equality, we can assume for contradiction that `x <> x'`.  The essential idea now is that we can remove either `x` and preserve surjectivity, leaving us with `n` elements and thus a surjection `Fin n -> Fin (S n)`.  Of course, there is some maneuvering that needs to be done to make the 'hole' left by removing `x` at `inl tt` so that we can create a function on the domain `Fin n`.
