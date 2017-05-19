---
layout: post
title: "Problem #1 Solution"
---

*[Problem #2 is here](https://coq-math-problems.github.io/Problem2/)*

*[Problem #2 Solution File](https://github.com/Coq-Math-Problems/Problems/blob/master/P2/P2_solution.v)*

**Infinite valleys `->` LPO**

Given `f : nat -> bool`, we can define the binary sequence which determines whether or not a `true` has occured at or below `x` in `f` as follows:

    Fixpoint true_below(f : nat -> bool)(x : nat) : bool :=
      match x with
      |0   => f 0
      |S y => f x || true_below f y
      end.

We can then turn that into a decreasing function `nat -> nat` as follows:

    Definition to_nat(f : nat -> bool) : nat -> nat := fun x => if f x then 0 else 1.
  
    Lemma to_nat_decr : forall f, decr (to_nat (true_below f)).

If we are assuming that any decreasing function has an infinite valley somewhere, we can look at the value an infinite valley (at, say, `x0`) takes for `to_nat (true_below f))`.  If it is `0`, then we know that `f` has a `true` somewhere, using the following lemma:

    Lemma true_below_correct1 : forall f x, true_below f x = true -> exists y, f y = true.

If it is `1`, then we can conclude that `f` is everywhere `false` as follows:  if `f x = true` for some `x`, then `true_below f y = true` for any `y` greater than `x`:

    Lemma true_below_correct2 : forall f x y, true_below f x = true -> x <= y -> true_below f y = true.

We can then prove that `true_below f (max x0 x)` has to be both `false` and `true`, a contradiction.

**LPO `->` Infinite valleys**

The strategy here for finding an infinite valley is much the same as our strategy for finding an `n`-valley in [problem 1](https://coq-math-problems.github.io/Problem1-Sol/):  Inducting on `f 0`, start at `0`, look if the value of `f` ever drops.  If it doesn't, we're done.  If it does, then use the inductive hypothesis.  Of course, the key problem for us is that you can't generally tell if a function's value ever drops.  However, we can if we have the LPO.

Given `f : nat -> nat`, we can produce a boolean-valued function that signifies whether or not `f` strictly decreases at a given point:

    Definition Slt(f : nat -> nat) : nat -> bool :=
      fun x => match lt_dec (f (S x)) (f x) with
               |left _  => true
               |right _ => false
               end.

(`lt_dec` is Coq's standard proof of the decidability of `<`)

Using LPO, we can then check if `Slt f` has a `true` or not.  If it does, then the value of `f` does drop; if not, then `f` is constant.  This is expressed in the following two lemmas:

    Lemma Slt_correct1 : forall f, decr f -> (forall x, Slt f x = false) -> forall x, f x = f 0.
    Lemma Slt_correct2 : forall f, decr f -> forall y, Slt f y = true -> f (S y) < f 0.
