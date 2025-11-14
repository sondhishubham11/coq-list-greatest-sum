Require Import Coq.Lists.List.
Require Import Coq.Init.Nat.
Require Import Plus.

(*Returns the updated pair of 2 greatest elements when
  a new element is compared with the current greatest elements*)
Definition update_greatest2 (new_elem : nat) (curr_elems : nat * nat) : (nat * nat) :=
  if ((fst curr_elems) <? new_elem) then
    (new_elem, fst curr_elems)
  else if ((snd curr_elems) <? new_elem) then
    (fst curr_elems, new_elem)
  else
    curr_elems.

(*Returns the two greatest elements of the list in a pair*)
Definition get_greatest2 (s : list nat) :=
  fold_right update_greatest2 (0, 0) s.

Definition pair_sum (a : nat * nat) : nat := fst a + snd a.

Definition add_greatest2 (s : list nat) : nat := pair_sum (get_greatest2 s).


(* --------------------------------------------------------------------------*)

(* The problem states that the lemma is given two elements a and b of the list
   but I want to include a hyposthesis in the context that those two elements are different 
   elements of the list.
   Adding a<>b in the context is wrong because it forces the specification 
   to choose unique natural numbers from the list and it would misbehave if there 
   is a repetition of the maximum element in the list *)

(* I could not choose two different elements of the list without using some 
   kind of unique identification of the list elements so, along with two elements
   from the list, the lemma also takes two indices in the range of the list *)


(* 
Don't really need this lemma
Lemma ind_of_greatest : forall (s : list nat) (a b : nat),
  1 <= length s -> get_greatest2 s = (a, b) -> 
    exists ind1, nth_error s ind1 = Some a.
Proof.
  induction s.
  + intros. inversion H.
  + intros. simpl in H. inversion H.
    (* For the case in which s is 0, index of the new element holds*)
    * exists 0. assert (s = nil). { destruct s. reflexivity. inversion H2. }
      rewrite H1 in*. simpl in*. unfold update_greatest2 in H0.
      simpl in*. destruct a. simpl in H0. inversion H0. reflexivity.
      simpl in H0. inversion H0. reflexivity.
    (* For the case in which s is not 0, use the induction hypothesis for the
       case in which the new element is not greater than the curr greatest*)
    * simpl in H0. destruct (get_greatest2 s) as []eqn:G2.
      unfold update_greatest2 in H0. simpl in H0.
      destruct (n <? a) as []eqn:Ena.
      (* use the index of the new element,0 in the case where new elem is
         greater than curr greatest*)
      - exists 0. simpl. inversion H0. reflexivity.
      (* use Induction hypothesis for the second case*)
      - apply (IHs n n0) in H2. 2 : { reflexivity. }
        destruct H2. exists (S x). simpl.
        destruct (n0 <? a). inversion H0. subst. apply H2.
        inversion H0. subst. apply H2.
Qed.
 *)


(* If the length of list is greater than 2, then the list must have two 
   greatest elements, didn't need to prove that the indices of those two elements
   are different *)
Lemma ind_of_greatest2 : forall (s : list nat) (a b : nat),
  2 <= length s -> get_greatest2 s = (a, b) -> 
    exists ind1 ind2, nth_error s ind1 = Some a /\ nth_error s ind2 = Some b.
Proof.
  induction s.
  + intros. inversion H.
  + intros. inversion H.
    * (* s is a list of single element, index of that single element
       and the new element which is added to the list depending upon
       their values are the required indices*)
      destruct s. inversion H2. destruct s.
      2 : { inversion H2. }
      clear H2. simpl in H0. destruct a.
      - destruct n. 
        ++ exists 0. exists 1. inversion H0. auto.
        ++ unfold update_greatest2 in H0. simpl in H0.
           inversion H0. exists 1. exists 0. auto.
      - destruct n. 
        ++ unfold update_greatest2 in H0. simpl in H0.
           inversion H0. exists 0. exists 1. auto.
        ++ unfold update_greatest2 in H0. simpl in H0.
           destruct (S n <? S a). 
           inversion H0. exists 0. exists 1. auto.
           inversion H0. exists 1. exists 0. auto.
    * (* For the case in which length of list is greater than 2,
       use the induction hypothesis and some case analysis when
       new element is greater than the current elems*)
      simpl in H0. destruct (get_greatest2 s) as []eqn:G2.
      apply (IHs n n0) in H2. 2 : { reflexivity. }
      unfold update_greatest2 in H0. simpl in H0.
      destruct H2. destruct H2. destruct H2.
      destruct (n <? a).
      - inversion H0. exists 0. exists (S x). subst. auto.
      - destruct (n0 <? a).
        ++ inversion H0. exists (S x). exists 0. subst. auto.
        ++ inversion H0. exists (S x). exists (S x0). subst. auto.
Qed.


(* The first element in the output of update_greatest2 is always
   greater than or equal to the first element of the input *)
Lemma update_ret_max : forall (a n n0 g1 g2 : nat),
  update_greatest2 a (n, n0) = (g1, g2) ->
    n <= g1.
Proof.
  intros. unfold update_greatest2 in H.
  simpl in H. destruct (n <? a) as []eqn:Hna.
  + apply PeanoNat.Nat.ltb_lt in Hna.
    (* Search (_ < _ -> _ <= _). *)
    apply PeanoNat.Nat.lt_le_incl in Hna.
    replace g1 with a. apply Hna. inversion H. auto.
  + assert (g1 = n). { destruct (n0 <? a). inversion H. auto. inversion H. auto. }
    rewrite H0. auto.
Qed.

(* The first element in the pair returned by get_greatest2 is greater than
   or equal to every element in the list *)
Lemma first_max : forall (s : list nat) (g1 g2 : nat),
  get_greatest2 s = (g1, g2) ->
    (forall (i a : nat), nth_error s i = Some a -> a <= g1).
Proof.
  induction s.
  + intros. destruct i. inversion H0. inversion H0.
  + intros. simpl in H. destruct (get_greatest2 s) as []eqn:G2.
    destruct i.
    - (* i = 0 means new element is being compared with the maximum element *)
      simpl in H0. inversion H0. rewrite <- H2.
      unfold update_greatest2 in H. destruct (fst (n, n0) <? a) as []eqn:Maxelem.
      * (* when new elem is greater than the current maximum, 
           new elem is compared with itself*) 
        simpl in H. inversion H. auto.
      * (* when new elem is not greater than the current maximum, it is
           smaller than or equal to the current maximum (what we need to prove)*)
        simpl in*. assert (g1 = n). { destruct (n0 <? a). inversion H. auto. inversion H. auto. }
        rewrite PeanoNat.Nat.ltb_antisym in Maxelem.
        unfold negb in Maxelem. assert (a <=? n = true).
        { destruct (a <=? n). auto. auto. }
        apply PeanoNat.Nat.leb_le in H3.
        rewrite H1. apply H3.
    - (* i <> 0 means we are not comparing the new element
         Use induction hypothesis for the other elements of the list*)
      simpl in H0. rewrite <- G2 in IHs.
      assert (a0 <= n). apply (IHs n n0 G2 i a0 H0).
      apply update_ret_max in H. (* Search (_ <= _ -> _ <= _ -> _ <= _). *)
      apply PeanoNat.Nat.le_trans with n. apply H1. apply H.
Qed.


(* If the first element in smaller than the new element that we feed to
  update_greatest2, 0 would be the only index which would return the
  greatest element in the new list*)
Lemma update_0index : forall (s : list nat) (a g1 g2 s1 s2 imax : nat),
  get_greatest2 (a :: s) = (g1, g2) -> get_greatest2 s = (s1, s2) ->
    (s1 <? a = true) -> nth_error (a :: s) imax = Some g1 -> imax = 0.
Proof.
  intros.
  assert ((forall (i k : nat), nth_error s i = Some k -> k <= s1)).
  apply first_max with s2. apply H0.
  simpl in H. rewrite H0 in H.
  unfold update_greatest2 in H. simpl in H.
  rewrite H1 in H. inversion H.
  destruct imax.
  + reflexivity.
  + (* Every element is less than or equal to the current greatest,
       and current greatest is less than the new element. The current greatest
       therefore cannot be greater than or equal to every element in the
       new list*)
    simpl in H2.
    apply PeanoNat.Nat.ltb_lt in H1.
    assert (forall i k : nat, nth_error s i = Some k -> k < a).
    {
      intros. assert (k <= s1). apply (H3 i k H4).
      (* Search (_ <= _ -> _ < _ -> _). *)
      apply (PeanoNat.Nat.le_lt_trans k s1 a H7 H1).
    }
    (* Search (_ < _ -> _ <> _). *)
    apply H4 in H2. 
    apply PeanoNat.Nat.lt_neq in H2.
    exfalso. unfold not in H2. apply H2.
    symmetry. apply H5.
Qed.

(* If the new element is neither greater than nor equal to the current greatest
   then the the index of the maximum element in the new list cannot be zero*)
Lemma no_update0_index : forall (s : list nat) (a g1 g2 s1 s2 imax : nat),
  get_greatest2 (a :: s) = (g1, g2) -> get_greatest2 s = (s1, s2) -> s1 <? a = false ->
    (s1 =? a = false) -> nth_error (a :: s) imax = Some g1 -> imax <> 0.
Proof.
  intros.
  simpl in*. rewrite H0 in H. unfold update_greatest2 in H.
  simpl in H. rewrite H1 in H.
  apply PeanoNat.Nat.eqb_neq in H2. unfold not in*.
  intros. rewrite H4 in H3.
  destruct (s2 <? a).
  + inversion H. simpl in H3. inversion H3.
    apply H2. subst. reflexivity.
  + inversion H. simpl in H3. inversion H3.
    apply H2. subst. reflexivity.
Qed.

(* If there exist two different elements in a list then the length of list must be
   greater than or equal to 2*)
Lemma elem2_length2 : forall (s : list nat) (ind1 ind2 a b: nat),
  (nth_error s ind1 = Some a) -> (nth_error s ind2 = Some b) -> ind1 <> ind2 ->
  2 <= length s.
Proof.
  intros.
  destruct s.
  + destruct ind1. inversion H. inversion H.
  + destruct s. destruct ind1.
    * destruct ind2. easy. destruct ind2. simpl in*. inversion H0. inversion H0.
    * destruct ind2. destruct ind1. simpl in*. inversion H. simpl in*. inversion H.
      destruct ind1. inversion H. inversion H.
    * simpl. replace (S (S (length s))) with (2 + (length s)).
      (* Search (_ -> _ <=_ + _). *) apply le_plus_l. reflexivity.
Qed.

(* Second elem is always less than or equal to the first element
   of get_greatest2*)
Lemma second_lte_first : forall (s : list nat) (g1 g2 : nat),
  get_greatest2 s = (g1, g2) -> g2 <= g1.
Proof.
  induction s.
  + intros. simpl in H. inversion H. auto.
  + intros. simpl in H. destruct (get_greatest2 s) as []eqn:G2.
    unfold update_greatest2 in H. simpl in H.
    destruct (n <? a) as []eqn:Ena.
    - inversion H. apply PeanoNat.Nat.ltb_lt in Ena.
      subst. apply PeanoNat.Nat.lt_le_incl. apply Ena.
    - destruct (n0 <? a) as []eqn:En0a.
      * inversion H. subst.
        apply PeanoNat.Nat.ltb_ge in Ena. apply Ena.
      * inversion H. subst. apply (IHs g1 g2). reflexivity.
Qed.


(* Second element in the pair returned by get_greatest2 is greater than or equal to every 
   element except when the value of the element being compared is equal to the value of the
   maximum element of the list(the first element of the pair retuned by get_greatest2)*)
Lemma second_max : forall (s : list nat) (g1 g2 imax: nat),
  get_greatest2 s = (g1, g2) -> nth_error s imax = Some g1 ->
    (forall (i a : nat), nth_error s i = Some a -> (i <> imax) -> (a <= g2)).
Proof.
  induction s.
  + intros. destruct i. inversion H1. inversion H1.
  + intros. destruct (get_greatest2 s) as []eqn:G2.
    destruct (n <? a) as []eqn:Fsmall.
    {
      (*Since the new element is greater than the greatest element of the
        current list, 0 would be the only element that can return the
        greatest element in the new list*)
      assert (imax = 0).
      apply (update_0index s a g1 g2 n n0 _).
      apply H. apply G2. apply Fsmall. apply H0.
      destruct i.
      + exfalso. unfold not in H2. apply H2. auto.
      + assert (forall (i a : nat), nth_error s i = Some a -> a <= n).
        apply first_max with n0. apply G2.
        simpl in*. apply H4 in H1.
        rewrite G2 in H. unfold update_greatest2 in H.
        simpl in H. rewrite Fsmall in H. inversion H.
        rewrite <- H7. apply H1.
    }
    destruct (n0 <? a) as []eqn:Ssmall.
    {
      destruct (n =? a) as []eqn:Feq.
      {
        (*Since the second max element of the new list is equal to 
          first maximum, can use the first_max lemma*)
        assert ((forall (i k : nat), nth_error (a :: s) i = Some k -> k <= g1)).
        apply first_max with g2. apply H.
        simpl in H. rewrite G2 in H. unfold update_greatest2 in H.
        simpl in*. rewrite Fsmall in H. rewrite Ssmall in H. inversion H.
        apply PeanoNat.Nat.eqb_eq in Feq. rewrite <- H5 in H3.
        rewrite Feq in H3. rewrite H6 in H3. apply H3 with i.
        rewrite <- H6. apply H1.
      }
      {
        (*Use the fact that imax can't be 0 since the new element added
          to the list is less than the current maximum*)
        assert (imax <> 0).
        { apply (no_update0_index s a g1 g2 n n0 imax H G2 Fsmall Feq H0). }
        destruct imax. easy. simpl in H0.
        destruct i.
        + (* for i = 0, second greatest element is the new element that we added*)
          simpl in*. rewrite G2 in H. unfold update_greatest2 in H. simpl in H.
          rewrite Fsmall in H. rewrite Ssmall in H. inversion H. inversion H1.
          subst. auto.
        + (* for i <> 0, use the induction hypothesis to prove a0 is less than
           the second element and the hypothesis that the new element
           that is greater than the second element*)
          simpl in*. rewrite G2 in H. unfold update_greatest2 in H.
          simpl in H. rewrite Fsmall in H. rewrite Ssmall in H.
          inversion H. rewrite <- H5 in H0. assert (a0 <= n0).
          apply (IHs n n0 imax) with i. reflexivity. rewrite H0.
          reflexivity. rewrite H1. reflexivity. auto.
          apply PeanoNat.Nat.ltb_lt in Ssmall. rewrite <- H6.
          (* Search (_ <= _ -> _ < _ -> _). *) assert (a0 < a).
          apply (PeanoNat.Nat.le_lt_trans a0 n0 a). apply H4. apply Ssmall.
          (* Search (_ < _ -> _ <= _). *)
          apply PeanoNat.Nat.lt_le_incl. apply H7.
      }
    }
    {
    destruct (n =? a) as []eqn:Feq.
    (* a is equal to the maximum element, and is less than or equal to
       the second greatest element. Use that to prove second greatest element
       is equal to greatest element*)
    {
      assert (g2 <= g1). apply (second_lte_first (a :: s)). apply H.
      assert (a0 <= g1). apply (first_max (a :: s) g1 g2) with i.
      apply H. apply H1. simpl in H. rewrite G2 in H.
      unfold update_greatest2 in H. simpl in H.
      rewrite Fsmall in H. rewrite Ssmall in H.
      inversion H. subst.
      apply PeanoNat.Nat.ltb_ge in Fsmall.
      apply PeanoNat.Nat.ltb_ge in Ssmall.
      apply PeanoNat.Nat.eqb_eq in Feq.
      rewrite Feq in H3.
(*    Search (_ <= _ -> _ <= _ -> _).*)
      apply PeanoNat.Nat.le_antisymm in H3.
      subst. apply H4. apply Ssmall.
    }
    {
      (* use the fact that imax cannot be zero
       and then use induction hypothesis for the list *)
      assert (imax <> 0).
      { apply (no_update0_index s a g1 g2 n n0 imax H G2 Fsmall Feq H0). }
      destruct i.
      + (* For i = 0, use the fact that new elem is smaller than the second element*)
        simpl in*. rewrite G2 in H. unfold update_greatest2 in H.
        simpl in H. rewrite Fsmall in H. rewrite Ssmall in H.
        inversion H. inversion H1. subst.
        apply PeanoNat.Nat.ltb_ge in Ssmall.
        apply Ssmall.
      + (* For i <> 0, use the induction hypothesis*)
        destruct imax. easy.
        simpl in*. rewrite G2 in H. unfold update_greatest2 in H.
        simpl in H. rewrite Fsmall in H. rewrite Ssmall in H. inversion H.
        subst. apply (IHs g1 g2 imax) with i. reflexivity.
        apply H0. apply H1. auto.
    }
   }
Qed.

(* Merget the first_max and second_max lemmas*)
Lemma get_greatest2_correct : forall (s : list nat) (g1 g2 imax imax2: nat),
  get_greatest2 s = (g1, g2) -> nth_error s imax = Some g1 -> nth_error s imax2 = Some g2 ->
    (forall (i a : nat), nth_error s i = Some a -> a <= g1) /\
      (forall (i a : nat), nth_error s i = Some a -> (i <> imax) -> (a <= g2)).
Proof.
  split.
  + apply first_max with g2. apply H.
  + apply second_max with g1. apply H. apply H0.
Qed.

(* The ind1 and ind2 are in the range of list is taken care of by the nth_error*)
Lemma add_greatest2_correct : forall (s : list nat) (ind1 ind2 a b: nat),
  (nth_error s ind1 = Some a) -> (nth_error s ind2 = Some b) -> ind1 <> ind2 ->
    a + b <= add_greatest2 s.
Proof.
  intros. unfold add_greatest2.
  destruct (get_greatest2 s) as []eqn:G2.
  assert (exists ind1 ind2, nth_error s ind1 = Some n /\ nth_error s ind2 = Some n0).
  {
    apply ind_of_greatest2.
    apply (elem2_length2 s ind1 ind2 a b H H0 H1). apply G2.
  }
  destruct H2. destruct H2. destruct H2.
  apply (get_greatest2_correct s n n0 x x0) in G2. destruct G2.
  unfold pair_sum. simpl.
  destruct (ind1 =? x) as []eqn:Hmax.
  {
    (* when an index of one of the element is equal to the index of greatest element 
       then compmare it with the greatest element, and compare the second element with the
       second greatest element. Since the second element cannot have the same index as the
       first one, it cannot have index of the greatest element. So, we can use
       second_max lemma *)
    apply PeanoNat.Nat.eqb_eq in Hmax.
    assert (a <= n). apply H4 with ind1. apply H.
    apply H5 in H0.
    + (*Search (_ -> _ + _ <= _ + _).*)
      apply plus_le_compat.
      apply H6. apply H0.
    + rewrite <- Hmax. auto.
  }
  {
    (* The index of one of the elements that we are comparing does not have the index of the
       greatest element. Compare this element to the second greatest element and the other
       element to the greatest element*)
    apply PeanoNat.Nat.eqb_neq in Hmax.
    assert (b <= n). apply H4 with ind2. apply H0.
    apply H5 in H.
    - replace (a + b) with (b + a). apply plus_le_compat.
      apply H6. apply H. apply plus_comm.
    - apply Hmax.
  }
  apply H2. apply H3.
Qed.

(* ---------------------------------------------------------------------------------*)

(* I think the Lemma is incomplete. It should also specify that there should exist 
   atlest one pair of different elements of the list whose sum should be equal to the
   add_greatest2 s to consider the function verified *)

Lemma add_greatest2_correct' : forall (s : list nat) (ind1 ind2 a b: nat),
  (nth_error s ind1 = Some a) -> (nth_error s ind2 = Some b) -> ind1 <> ind2 ->
    (a + b <= add_greatest2 s /\ (exists i1 i2 k1 k2, nth_error s i1 = Some k1 ->
      nth_error s i2 = Some k2 -> i1 <> i2 -> k1 + k2 = add_greatest2 s)).
Proof.
  intros. split. 
  + apply (add_greatest2_correct s ind1 ind2). apply H. apply H0. apply H1.
  + destruct (get_greatest2 s) as []eqn:G2.
    assert (exists ind1 ind2, nth_error s ind1 = Some n /\ nth_error s ind2 = Some n0).
    {
      apply ind_of_greatest2.
      apply (elem2_length2 s ind1 ind2 a b H H0 H1). apply G2.
    }
    destruct H2. destruct H2. destruct H2.
    exists x. exists x0. exists n. exists n0.
    intros. unfold add_greatest2. rewrite G2. reflexivity.
Qed.


(*-----------------------------------------------------------------------------------*)

(* I probably would not use the same approach if efficiency is an issue. 
   Maintaining a list of n greatest elements through the entire list would 
   have complexity of O((length list) * n). Instead, I would use a standard 
   sorting algorithm like Quick sort which has an average complexity of 
   O((length list) * log (length list)). And then pick the first n elements 
   (if the quick sort was used to arrange the list in descending order) and return their sum.

  For the proof of correctness of this function, I would first prove a lemma about the
  output of the sorting function that returns a list in decreasing order :

  Lemma sorting_correct : forall (s : list nat) (i1 i2 k1 k2 : nat)
    nth_error s i1 = Some k1 -> nth_error i2 = Some k2 -> i1 < i2 -> k2 <= k1.
  I believe this would be difficult to prove for Quick Sort since the straightforward
  induction would not generate a hypothesis which is directly useful. Honestly, I don't 
  even have a rough proof sketch in my mind at the moment. This would probably make the
  proof much harder, for me.

  The second lemma that I would need would say if there are n different indices in the 
  given list, then there would exist n different indices corresponding to the same elements
  in the sorted list too. Then I would use this lemma to extract the indices for the new sorted list.
  This would again be very difficult like the first lemma because the normal induction would
  not generate directly useful hypothesis.

  Since the elements corresponding to these indices are same, the sum of the elements 
  corresponding to these indices should also be same. This lemma should be easy to prove.

  Once I have these lemmas, my very high level idea for the proof is to compare the
  indices of the given elements with 0 1....n indices. For every element I would use 
  destruct on "k <=? n" where k is the index of the element in the sorted list 
  (equivalent to (imax =? 0) in the previous proof)
  If it is true than the element at index k is equal to element at index k.
  Otherwise it is less than or equal to every element of the n greatest elements, using
  the sorting_correct lemma.
  This is probably going to be a lot harder (but doable for me) than the previous proof
  for 2 elements. I would probably need the hypothesis that the elements are different
  to prevent the overlapping of the indices for different elements.

  This is a very high level idea. I am pretty sure that I would run into problems that I 
  have not anticipated especially while comparing the indices of the elements with 
  0 1 2..n indices and probably end up changing the idea a little while writing the actual proof.
*)


(*---------------------------------------------------------------------------------------*)

 (* I haven't worked with extraction at all so, my solutions might sound newbie.
    I think Coq nat does not have any upper bound and the Coq function does not say anything
    about the overflow. In the case of overflow, the extracted function and the Coq function
    would behave differently and the theorems that we proved on the Coq function would not
    hold for the extracted function.

    At CertiK, they had defined a dataype int64 that correspond to 64 bit integer of Rust.
    It had an upper bound and the operations defined on int64 imitated the Rust operations.

    We could do something similar, define a new datatype with range and operations on the
    that exactly imitate the operations on natural numbers in OCaml.
    Then use this new datatype instead of Coq nat.

    For the list, we could also define a new datatype which would imitate the OCaml list with
    maximum number of elements that it could hold. The insert or other operations that 
    increase the size of the list would imitate the changes that the OCaml operations make
    in case the size of the list increases the maximum range.
    We do not increase the size of the list in our current function. So, I think instead of
    making a new data type we could add in the specification that the length of the
    list is not greater than 10^6.
    We can also do this for elements in the list but we would have to mention this at a lot of
    different places and I would probably miss to include this for some element or operation.
    I believe it is better to make a new data type corresponding to the natural numbers of OCaml
    instead of mentioning everywhere in the specification that the value of nat is less than 2^30.
*)


