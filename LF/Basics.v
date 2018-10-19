(******* Some definitions taken from explaination ***********)
Definition negb (b:bool) : bool :=
  match b with
  | true => false
  | false => true
  end.

Definition andb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.

Definition orb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => true
  | false => b2
  end.

(**********************************************************************************)
(******* Exercise: 1 star (nandb)  ************************************************)
(**********************************************************************************)

Definition nandb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | false => true
  | true => match b2 with
            | true => false
            | false => true
            end
  end.

Example test_nandb1:               (nandb true false) = true.
Proof. simpl. reflexivity. Qed. 
Example test_nandb2:               (nandb false false) = true.
Proof. simpl. reflexivity. Qed. 
Example test_nandb3:               (nandb false true) = true.
Proof. simpl. reflexivity. Qed. 
Example test_nandb4:               (nandb true true) = false.
Proof. simpl. reflexivity. Qed. 

Check nandb.
(**********************************************************************************)







(**********************************************************************************)
(******* Exercise: 1 star (nandb)  ************************************************)
(**********************************************************************************)

Definition andb3 (b1:bool) (b2:bool) (b3:bool) : bool :=
  andb (andb b1 b2) b3.

Example test_andb31:                 (andb3 true true true) = true.
Proof. simpl. reflexivity. Qed. 
Example test_andb32:                 (andb3 false true true) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb33:                 (andb3 true false true) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb34:                 (andb3 true true false) = false.
Proof. simpl. reflexivity. Qed.

Check andb3.
(*********************************************************************************)






(**********************************************************************************)
(******* Exercise: 1 star (factorial) *********************************************)
(**********************************************************************************)

Fixpoint plus (n : nat) (m : nat) : nat := (* Take this definition from text *)
  match n with
    | O => m
    | S n' => S (plus n' m)
  end.

Fixpoint mult (n m : nat) : nat := (* Take this definition from text *)
  match n with
    | O => O
    | S n' => plus m (mult n' m)
  end.

Fixpoint factorial (n:nat) : nat :=
  match n with
  | O => 1
  | S m => mult (S m) (factorial m)
  end.

Example test_factorial1:          (factorial 3) = 6.
Proof. simpl. reflexivity. Qed.
Example test_factorial2:          (factorial 5) = (mult 10 12).
Proof. simpl. reflexivity. Qed.

Check factorial.

(**********************************************************************************)







(**********************************************************************************)
(******* Exercise: 1 star (blt_nat) ***********************************************)
(**********************************************************************************)

(** We are required to use previously defined functions to define blt_nat**)
(** I thought to use minus to check inequality*)

Fixpoint minus (n m:nat) : nat :=   (* Take this definition from text*)
  match n, m with
  | O   , _    => O
  | S _ , O    => n
  | S n', S m' => minus n' m'
  end.


Definition blt_nat (n m : nat) : bool := 
  match minus m n with
  | O => false
  | S n' => true
  end.

(* See that in our definition, minus X Y is zero if  X is less than or equal to Y *)

Example test_blt_nat1:             (blt_nat 2 2) = false.
Proof. simpl. reflexivity. Qed.
Example test_blt_nat2:             (blt_nat 2 4) = true.
Proof. simpl. reflexivity. Qed.
Example test_blt_nat3:             (blt_nat 4 2) = false.
Proof. simpl. reflexivity. Qed.

Check blt_nat.

(**********************************************************************************)







(**********************************************************************************)
(******* Exercise: 1 star (plus_id_exercise) **************************************)
(**********************************************************************************)

Theorem plus_id_exercise : forall n m o : nat,
  n = m -> m = o -> n + m = m + o.
Proof. intros n m o.  (* We have considered 2 hypothesis so we need to intro & rewrite twice*)
       intros H H'.
       rewrite -> H.
       simpl.
       rewrite -> H'. 
       reflexivity.
Qed.
(**********************************************************************************)







(**********************************************************************************)
(******* Exercise: 2 stars (mult_S_1) *********************************************)
(**********************************************************************************)

Theorem mult_S_1 : forall n m : nat,
  m = S n ->
  m * (1 + n) = m * m.
Proof. intros n m. 
       intros H. 
       simpl. 
       rewrite -> H.
       reflexivity. 
Qed.
 
(**********************************************************************************)







(**********************************************************************************)
(******* Exercise: 2 stars (andb_true_elim2) **************************************)
(**********************************************************************************)

Theorem andb_true_elim2 : forall b c : bool,
  andb b c = true -> c = true.
Proof. 
  intros [] [].
  - reflexivity. 
  - simpl. intros H. rewrite -> H. reflexivity. 
  - reflexivity.
  - simpl. intros H. rewrite -> H. reflexivity. 
Qed.
 
(**********************************************************************************)








(**********************************************************************************)
(******* Exercise: 1 star (zero_nbeq_plus_1) **************************************)
(**********************************************************************************)

Fixpoint beq_nat (n m : nat) : bool := (* Take this from text. *)
  match n with
  | O => match m with
         | O => true
         | S m' => false
         end
  | S n' => match m with
            | O => false
            | S m' => beq_nat n' m'
            end
  end.

Theorem zero_nbeq_plus_1 : forall n : nat,
  beq_nat 0 (n + 1) = false.
Proof.
  intros n. destruct n.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.
(**********************************************************************************)








(**********************************************************************************)
(*                              MORE EXERCISES                                    *)
(**********************************************************************************)


(**********************************************************************************)
(******* Exercise: 2 stars (boolean_functions) ************************************)
(**********************************************************************************)
Theorem identity_fn_applied_twice : forall (f : bool -> bool),
  (forall (x : bool), f x = x) -> forall (b : bool), f (f b) = b.
Proof.
  intros f x b. 
  rewrite -> x. rewrite  -> x. reflexivity.
Qed.

(**********************************************************************************)






(**********************************************************************************)
(******* Exercise: 3 stars  optional (andb_eq_orb) ********************************)
(**********************************************************************************)
Theorem andb_eq_orb :
  forall (b c : bool),
  (andb b c = orb b c) ->
  b = c.
Proof.
  intros [] [].
  - reflexivity.
  - simpl. intros H. rewrite -> H. reflexivity.
  - simpl. intros H. rewrite -> H. reflexivity.
  - reflexivity.
Qed.
(**********************************************************************************)





(**********************************************************************************)
(******* Exercise: 3 stars (binary) ***********************************************)
(**********************************************************************************)

Inductive binary : Type :=
           | zero :  binary
           | Twice : binary -> binary
           | Twice_plus_one : binary -> binary.


Fixpoint plus' (n : nat) (m : nat) : nat := (* Take this definition from text *)
  match n with
    | O => m
    | S n' => S (plus' n' m)
  end.

Fixpoint mult' (n m : nat) : nat := (* Take this definition from text *)
  match n with
    | O => O
    | S n' => plus' m (mult' n' m)
  end.

Fixpoint incr' (n : nat) : nat := (* Take this definition from text *)
 plus 1 n.

(*
Fixpoint plus_bin (n : binary) (m : binary) : binary := 
  match n with
    | zero => m
    | Twice n' => match m with
                  | zero => n
                  | Twice m' => Twice ( plus_bin n' m')
                  | Twice_plus_one m' => Twice_plus_one ( plus_bin n' m')
                  end
    | Twice_plus_one n' => match m with
                  | zero => n
                  | Twice m' => Twice_plus_one ( plus_bin n' m')
                  | Twice_plus_one m' => Twice_plus_one ( plus_bin n' m') 

                     (* ^ Rethink at this step !!! *)

                   end
  end. 
*)

Fixpoint incr (n : binary) : binary :=
  match n with
  | zero => Twice_plus_one zero
  | Twice n' => Twice_plus_one n'
  | Twice_plus_one n' => Twice (incr n')
  end.


Fixpoint bin_to_nat (n : binary) : nat :=
  match n with
  | zero => 0
  | Twice n' => mult' 2 (bin_to_nat n')
  | Twice_plus_one n' => plus 1 (mult' 2 (bin_to_nat n'))
end.

Compute(incr zero).
Check incr.
Check bin_to_nat.

Example test1 : bin_to_nat( incr (Twice_plus_one ( Twice_plus_one (Twice_plus_one zero)))) = 8.
Proof. simpl. reflexivity. Qed.

Theorem checks_conversion :(forall (x : binary), incr' (bin_to_nat x) = bin_to_nat (incr x) ). 
Proof.
  intros x. destruct x.
  - reflexivity.
  - simpl.  Admitted.

(* I thought of writing a theorem and then proving it. I am unsuccessful till now int
   doing so but will try to complete this.
*)

(**********************************************************************************)
