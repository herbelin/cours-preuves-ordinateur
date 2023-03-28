Require Export Languages.
Import ListNotations.

(** * Regular expressions (regexps) on finite ordered letters *)

Module Type FiniteOrderedType.
 (* Ask for a type [t], an order [lt], a boolean test [eqb], etc *)
 Include UsualOrderedType' <+ HasEqBool.
 (* Moreover, [t] is finite. *)
 Parameter enumeration : list t.
 Parameter enumeration_spec : forall x:t, In x enumeration.
End FiniteOrderedType.

Module Regexps (Letter : FiniteOrderedType).

 (* For LetterB.eqb_spec, LetterB.eqb_neq, ... *)
 Module LetterB := BoolEqualityFacts(Letter).

 Definition word := list Letter.t.

 Implicit Types a : Letter.t.
 Implicit Types w : word.

 (** ** Regexps : definition *)

 Inductive re :=
  | Void : re
  | Epsilon : re
  | Letter : Letter.t -> re
  | Cat : re -> re -> re
  | Star : re -> re
  | Or : re -> re -> re
  | And : re -> re -> re
  | Not : re ->  re.

 (** ** Language of a regexp **)

 Module Lang := Languages.Lang(Letter).
 Import Lang.Notations.
 Open Scope lang_scope.

 Fixpoint lang r : Lang.t :=
  match r with
  | Void => ∅
  | Epsilon => ε
  | Letter a => a
  | Cat r s => lang r · lang s
  | Star r => (lang r)★
  | Or r s => lang r ∪ lang s
  | And r s => lang r ∩ lang s
  | Not r =>  ¬lang r
  end.

 (** ** Nullable regexp : definition **)

 Fixpoint is_nullable (r : re) : bool :=
  match r with
  | Epsilon | Star _ => true
  | Void | Letter _ => false
  | Cat r s | And r s => is_nullable r && is_nullable s
  | Or r s => is_nullable r || is_nullable s
  | Not r => negb (is_nullable r)
  end.

 Lemma nullable_ok r : is_nullable r = true <-> lang r [].
 Proof.
 Admitted.

 Lemma nullable_spec r : reflect (lang r []) (is_nullable r).
 Proof.
 apply iff_reflect. symmetry. apply nullable_ok.
 Qed.


 (** ** Derivative of a regular expression **)
 
 Declare Scope re_scope.
 Bind Scope re_scope with re.
 Delimit Scope re_scope with re.
 Open Scope re_scope.

 (** deriv1 : derivative by a letter *)

 Fixpoint deriv1 r a :=
  match r with
  | Void => Void
  | Epsilon => Void
  | Letter a' => if Letter.eqb a a' then Epsilon else Void
  | Cat r s =>
    Or (Cat (deriv1 r a) s) (if is_nullable r then deriv1 s a else Void)
  | Star r => Cat (deriv1 r a) (Star r)
  | Or r s => Or (deriv1 r a) (deriv1 s a)
  | And r s => And (deriv1 r a) (deriv1 s a)
  | Not r => Not (deriv1 r a)
  end.

 Infix "/" := deriv1 : re_scope.

 (** deriv : derivative by a word, ie many letters *)

 Fixpoint deriv r w :=
  match w with
  | [] => r
  | a::w' => deriv (r/a) w'
  end.

 Infix "//" := deriv (at level 40) : re_scope.

 Lemma deriv1_ok r a : lang (r/a) == Lang.derivative (lang r) [a].
 Proof.
 Admitted.

 Lemma deriv_ok r w : lang (r//w) == Lang.derivative (lang r) w.
 Proof.
 Admitted.

 Lemma deriv1_ok' r a w : lang (r/a) w <-> lang r (a::w).
 Proof.
 Admitted.

 Lemma deriv_ok' r w w' : lang (r//w) w' <-> lang r (w++w').
 Proof.
 Admitted.

(** ** Matching : is a word in the language of a regexp ? *)

 Definition matching r w := is_nullable (r//w).

 Lemma matching_ok r w : matching r w = true <-> lang r w.
 Proof.
 Admitted.

 (** We can now prove that being in [lang r] is decidable *)

 Lemma lang_dec r w : { lang r w } + { ~lang r w }.
 Proof.
 destruct (matching r w) eqn:E; [left|right];
  rewrite <- matching_ok; auto.
 intros E'. now rewrite E' in E.
 Qed.

 (** Derivative of a regexp : properties **)

 Lemma deriv_void w : Void // w = Void.
 Proof.
 Admitted.

 Lemma deriv_epsilon w : In (Epsilon // w) [Void; Epsilon].
 Proof.
 Admitted.

 Lemma deriv_letter a w :
  In (Letter a // w) [Void; Epsilon; Letter a].
 Proof.
 Admitted.

 Lemma deriv_or r s w :
  (Or r s) // w = Or (r//w) (s//w).
 Proof.
 Admitted.

 Lemma deriv_and r s w :
  (And r s) // w = And (r // w) (s // w).
 Proof.
 Admitted.

 Lemma deriv_not r w :
  (Not r) // w = Not (r // w).
 Proof.
 Admitted.

 Lemma deriv_app r w w' :
  r // (w++w') = r // w // w'.
 Proof.
 Admitted.

 (** ** Equivalence of regexps *)

 Definition equiv r s := lang r == lang s.

 Infix "===" := equiv (at level 70).

 (** A few technical declarations for being able to rewrite with === *)

 Global Instance : Equivalence equiv.
 Proof. firstorder. Qed.
 Global Instance : Proper (equiv ==> equiv ==> equiv) Or.
 Proof. firstorder. Qed.
 Global Instance : Proper (equiv ==> equiv ==> equiv) And.
 Proof. firstorder. Qed.
 Global Instance : Proper (equiv ==> equiv ==> equiv) Cat.
 Proof. firstorder. Qed.
 Global Instance : Proper (equiv ==> equiv) Not.
 Proof. firstorder. Qed.
 Global Instance : Proper (equiv ==> equiv) Star.
 Proof. intros r r' E. unfold "===" in *. simpl. now rewrite E. Qed.
 Global Instance : Proper (equiv ==> eq) is_nullable.
 Proof. intros r r' E. apply eq_true_iff_eq. rewrite !nullable_ok; auto. Qed.
 Global Instance : Proper (equiv ==> eq ==> equiv) deriv1.
 Proof. intros r r' E a a' <- w. rewrite !deriv1_ok'; auto. Qed.
 Global Instance : Proper (equiv ==> eq ==> equiv) deriv.
 Proof. intros r r' E w w' <- w2. rewrite !deriv_ok'; auto. Qed.
 Global Instance : Proper (equiv ==> eq ==> eq) matching.
 Proof. intros r r' E w w' <-. unfold matching. now rewrite E. Qed.

 Lemma or_comm r s : Or r s === Or s r.
 Proof.
 Admitted.

 Lemma or_assoc r s t : Or (Or r s) t === Or r (Or s t).
 Proof.
 Admitted.

 Lemma or_idem r : Or r r === r.
 Proof.
 Admitted.

 Lemma or_void_l r : Or Void r === r.
 Proof.
 Admitted.

 Lemma or_void_r r : Or r Void === r.
 Proof.
 Admitted.

 Lemma and_comm r s : And r s === And s r.
 Proof.
 Admitted.

 Lemma and_assoc r s t : And (And r s) t === And r (And s t).
 Proof.
 Admitted.

 Lemma and_idem r : And r r === r.
 Proof.
 Admitted.

 Lemma cat_void_l r : Cat Void r === Void.
 Proof.
 Admitted.

 Lemma cat_void_r r : Cat r Void === Void.
 Proof.
 Admitted.

 Lemma cat_eps_l r : Cat Epsilon r === r.
 Proof.
 Admitted.

 Lemma cat_eps_r r : Cat r Epsilon === r.
 Proof.
 Admitted.

 Lemma cat_assoc r s t : Cat (Cat r s ) t === Cat r (Cat s t).
 Proof.
 Admitted.

 Lemma star_is_or r : Star r === Or Epsilon (Cat r (Star r)).
 Proof.
 Admitted.

 Lemma star_void : Star Void === Epsilon.
 Proof.
 Admitted.

 Lemma star_epsilon : Star Epsilon === Epsilon.
 Proof.
 Admitted.

 Lemma star_star r : Star (Star r) === Star r.
 Proof.
 Admitted.

 Lemma cat_star r : Cat (Star r) (Star r) === Star r.
 Proof.
 Admitted.

End Regexps.
