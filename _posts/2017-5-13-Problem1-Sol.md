---
layout: post
title: "Problem #1 Solution"
---

*[Problem #1 is here](https://coq-math-problems.github.io/Problem1/)*

*[Problem #1 Solution File](https://github.com/Coq-Math-Problems/Problems/blob/master/P1/P1_solution.v)*

Intuitively, the idea behind this solution is as follows:  Starting at `0`, take `n` steps along `f`.  If the value of `f` hasn't changed, then great, we're done.  Otherwise, we're at a lower position than at `0` and we repeat.  This process will then terminate in at most `f 0` such `n`-step walks.

To formalize this, the bulk of our proof will go into the following auxiliary lemma, from which the theorem follows immediately:

`Lemma valley_aux : forall y f x n, f x <= y -> decr f -> exists x', valley f n x'.`

This can be proven using induction on `y`.  When `y = 0`, it is obvious that `f` is constant beyond `x` (and thus, that we can find an arbitrarily large valley at `x`).  This is expressed in the following lemma:

`Lemma decr_0 : forall f x, decr f -> f x = 0 -> forall y, x <= y -> f y = 0.`

At the inductive step of the proof, we check if there is an `n`-valley at `x` (in which case the proof is done) or if the value of `f` has actually dropped (in which case we can use the inductive hypothesis).  We can perform this check using the following lemma:

`Lemma valley_or_drop : forall n f x, decr f -> valley f n x \/ exists y, f y < f x.`

This is proven using a straightforward induction on `n`.
