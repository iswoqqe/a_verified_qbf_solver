theory Solver
  imports Main
begin

(*** QDIMACS-like data structure / PCNF format ***)
(*
We only store the top level quantifiers since they are required to be alternating in prefix.
Otherwise the encoding is straightforward.  There is however some cases where a formula can be
encoded using the below data structure, but not using QDIMACS:
- There is a quantified variable that does not occur in the matrix.
- There is a quantified variable that occurs multiple times in the matrix.
- The innermost quantified set is universal.
*)

datatype literal = P nat | N nat
type_synonym clause = "literal list"
type_synonym matrix = "clause list"

type_synonym quant_set = "nat \<times> nat list"
type_synonym quant_sets = "quant_set list"
datatype prefix =
UniversalFirst quant_set quant_sets |
ExistentialFirst quant_set quant_sets |
Empty

type_synonym pcnf = "prefix \<times> matrix"

(*** Alternative / Hos C30 format ***)
(*
PROBLEM: A potential problem with the above is that it is difficult (for me) to see how the simple
solver from the project plan could be implemented without making it identical to the definition of
the semantics.
OTHER IDEA: Encode a generic QBF formula.  This will allow us to use semantics directly from the
book.  The solver could then, for example, return `None` (or whatever it is called in Isabelle) if
the formula is not in PCNF.
SUMMARY: Encode any formula, only solve PCNF formulas.
*)

(* generic QBF formula *)
datatype QBF =
Var nat |
Neg QBF |
Conj "QBF list" |
Disj "QBF list" |
Ex nat QBF |
All nat QBF

(*** Semantics based on HoS C30 ***)
(* Substitute a variable for True or False. *)
fun substitute_var :: "nat \<Rightarrow> bool \<Rightarrow> QBF \<Rightarrow> QBF" where
"substitute_var z True (Var z') = (if z = z' then Conj [] else Var z')" |
"substitute_var z False (Var z') = (if z = z' then Disj [] else Var z')" |
"substitute_var z b (Neg qbf) = Neg (substitute_var z b qbf)" |
"substitute_var z b (Conj qbf_list) = Conj (map (substitute_var z b) qbf_list)" |
"substitute_var z b (Disj qbf_list) = Disj (map (substitute_var z b) qbf_list)" |
"substitute_var z b (Ex x qbf) = Ex x (if x = z then qbf else substitute_var z b qbf)" |
"substitute_var z b (All y qbf) = All y (if z = y then qbf else substitute_var z b qbf)"

(* Measures number of QBF constructors in argument, required to show termination of semantics. *)
fun qbf_measure :: "QBF \<Rightarrow> nat" where
"qbf_measure (Var _) = 1" |
"qbf_measure (Neg qbf) = 1 + qbf_measure qbf" |
"qbf_measure (Conj qbf_list) = 1 + sum_list (map qbf_measure qbf_list)" |
"qbf_measure (Disj qbf_list) = 1 + sum_list (map qbf_measure qbf_list)" |
"qbf_measure (Ex _ qbf) = 1 + qbf_measure qbf" |
"qbf_measure (All _ qbf) = 1 + qbf_measure qbf"

(* Substituting a variable does not change the QBF measure. *)
lemma qbf_measure_substitute: "qbf_measure (substitute_var z b qbf) = qbf_measure qbf"
proof (induction qbf)
  case (Var x)
  show "qbf_measure (substitute_var z b (Var x)) = qbf_measure (Var x)"
  proof (cases b)
    case True
    thus ?thesis by simp
  next
    case False
    thus ?thesis by simp
  qed
next
  case (Neg qbf)
  thus "qbf_measure (substitute_var z b (Neg qbf)) = qbf_measure (Neg qbf)" by simp
next
  case (Conj qbf_list)
  thus "qbf_measure (substitute_var z b (Conj qbf_list)) = qbf_measure (Conj qbf_list)"
  proof (induction qbf_list)
    case Nil
    thus "qbf_measure (substitute_var z b (Conj [])) = qbf_measure (Conj [])" by simp
  next
    case (Cons x xs)
    thus "qbf_measure (substitute_var z b (Conj (x # xs))) = qbf_measure (Conj (x # xs))" by simp
  qed
next
  case (Disj qbf_list)
  thus "qbf_measure (substitute_var z b (Disj qbf_list)) = qbf_measure (Disj qbf_list)"
  proof (induction qbf_list)
    case Nil
    thus "qbf_measure (substitute_var z b (Disj [])) = qbf_measure (Disj [])" by simp
  next
    case (Cons x xs)
    thus "qbf_measure (substitute_var z b (Disj (x # xs))) = qbf_measure (Disj (x # xs))" by simp
  qed
next
  case (Ex x qbf)
  thus "qbf_measure (substitute_var z b (QBF.Ex x qbf)) = qbf_measure (QBF.Ex x qbf)" by simp
next
  case (All y qbf)
  thus "qbf_measure (substitute_var z b (QBF.All y qbf)) = qbf_measure (QBF.All y qbf)" by simp
qed

(* The measure of an element in a disjunction/conjunction is less than the measure of the
disjunction/conjunction. *)
lemma qbf_measure_lt_sum_list:
  assumes "qbf \<in> set qbf_list"
  shows "qbf_measure qbf < Suc (sum_list (map qbf_measure qbf_list))"
proof -
  obtain left right where "left @ qbf # right = qbf_list" by (metis assms split_list)
  hence "sum_list (map qbf_measure qbf_list)
        = sum_list (map qbf_measure left) + qbf_measure qbf + sum_list (map qbf_measure right)"
    by fastforce
  thus "qbf_measure qbf < Suc (sum_list (map qbf_measure qbf_list))" by simp
qed

function qbf_semantics :: "(nat \<Rightarrow> bool) \<Rightarrow> QBF \<Rightarrow> bool" where
"qbf_semantics I (Var z) = I z" |
"qbf_semantics I (Neg qbf) = (\<not>(qbf_semantics I qbf))" |
"qbf_semantics I (Conj qbf_list) = list_all (qbf_semantics I) qbf_list" |
"qbf_semantics I (Disj qbf_list) = list_ex (qbf_semantics I) qbf_list" |
"qbf_semantics I (Ex x qbf) = ((qbf_semantics I (substitute_var x True qbf))
                              \<or> (qbf_semantics I (substitute_var x False qbf)))" |
"qbf_semantics I (All x qbf) = ((qbf_semantics I (substitute_var x True qbf))
                               \<and> (qbf_semantics I (substitute_var x False qbf)))"
  by pat_completeness auto
termination
  apply (relation "measure (\<lambda>(I,qbf). qbf_measure qbf)")
  by (auto simp add: qbf_measure_substitute qbf_measure_lt_sum_list)

(* Simple tests *)
definition "test_qbf = (All 3 (Conj [Disj [Neg (Var 2), Var 3, Var 1], Disj [Neg (Var 1), Var 2]]))"
value "substitute_var 1 False test_qbf"
value "substitute_var 1 True test_qbf"
value "substitute_var 2 False test_qbf"
value "substitute_var 2 True test_qbf"
value "substitute_var 3 False test_qbf"
value "substitute_var 3 True test_qbf"
value "qbf_semantics (\<lambda>x. False) test_qbf"
value "qbf_semantics ((\<lambda>x. False)(2 := True)) test_qbf"
value "qbf_semantics (((\<lambda>x. False)(2 := True))(1 := True)) test_qbf"

(* Satisfiability *)
definition satisfiable :: "QBF \<Rightarrow> bool" where
"satisfiable qbf = (\<exists>I. qbf_semantics I qbf)"

definition logically_eq :: "QBF \<Rightarrow> QBF \<Rightarrow> bool" where
"logically_eq qbf1 qbf2 = (\<forall>I. qbf_semantics I qbf1 = qbf_semantics I qbf2)"

(*** Conversion functions, left-inverses thereof, and proofs of the left-inverseness. ***)
(* Convert literal *)
fun convert_literal :: "literal \<Rightarrow> QBF" where
"convert_literal (P z) = Var z" |
"convert_literal (N z) = Neg (Var z)"

fun convert_literal_inv :: "QBF \<Rightarrow> literal option" where
"convert_literal_inv (Var z) = Some (P z)" |
"convert_literal_inv (Neg (Var z)) = Some (N z)" |
"convert_literal_inv _ = None"

lemma literal_inv: "convert_literal_inv (convert_literal lit) = Some lit"
  by (cases lit) auto

(*
(* like `sequence . map` == `mapM` in Haskell *)
fun sequence_map :: "('a \<Rightarrow> 'b option) \<Rightarrow> 'a list \<Rightarrow> 'b list option" where
"sequence_map f list =
  foldr (\<lambda>el acc. Option.bind (f el) (\<lambda>e. Option.bind acc (\<lambda>a. Some (e # a)))) list (Some [])" 

value "sequence_map convert_literal_inv [Var 2, Var 3, Neg (Var 4)]"
value "sequence_map convert_literal_inv [Var 2, Var 3, Neg (Var 4), Conj []]"
*)
(* like sequence in haskell specialized for option types *)
fun sequence_aux :: "'a option list \<Rightarrow> 'a list \<Rightarrow> 'a list option" where
"sequence_aux [] list = Some list" |
"sequence_aux (Some x # xs) list = sequence_aux xs (x # list)" |
"sequence_aux (None # xs) list = None"

fun sequence :: "'a option list \<Rightarrow> 'a list option" where
"sequence list = map_option rev (sequence_aux list [])"

(* Lemmas that are not needed at the moment: *)
(*lemma sequence_aux_no_None_not_None:
  assumes "list_all (\<lambda>x. x \<noteq> None) xs"
  shows "sequence_aux xs list \<noteq> None" using assms
proof (induction xs arbitrary: list)
  case Nil
  then show ?case by simp
next
  case (Cons y ys)
  then show "sequence_aux (y # ys) list \<noteq> None"
  proof (cases y)
    case None
    hence False using Cons by simp
    thus ?thesis by simp
  next
    case (Some a)
    hence "sequence_aux (y # ys) list = sequence_aux ys (a # list)" by simp
    thus ?thesis using Cons by simp
  qed
qed

lemma sequence_no_None_not_None: "list_all (\<lambda>x. x \<noteq> None) list \<Longrightarrow> sequence list \<noteq> None"
  using sequence_aux_no_None_not_None by auto*)

lemma list_no_None_ex_list_map_Some:
  assumes "list_all (\<lambda>x. x \<noteq> None) list"
  shows "\<exists>xs. map Some xs = list" using assms
proof (induction list)
  case Nil
  show "\<exists>xs. map Some xs = []" by simp
next
  case (Cons a list)
  from this obtain xs where "map Some xs = list" by fastforce
  moreover from Cons obtain x where "Some x = a" by fastforce
  ultimately have "map Some (x # xs) = a # list" by simp
  thus "\<exists>xs. map Some xs = a # list" by (rule exI)
qed

lemma sequence_aux_content: "sequence_aux (map Some xs) list = Some (rev xs @ list)"
proof (induction xs arbitrary: list)
  case Nil
  show "sequence_aux (map Some []) list = Some (rev [] @ list)" by simp
next
  case (Cons y ys)
  thus "sequence_aux (map Some (y # ys)) list = Some (rev (y # ys) @ list)" by simp
qed

lemma sequence_content: "sequence (map Some xs) = Some xs"
proof -
  have "sequence (map Some xs) = map_option rev (sequence_aux (map Some xs) [])" by simp
  moreover have "sequence_aux (map Some xs) [] = Some (rev xs @ [])"
    using sequence_aux_content by fastforce
  ultimately show "sequence (map Some xs) = Some xs" by simp
qed

(* Convert clause *)
fun convert_clause :: "clause \<Rightarrow> QBF" where
"convert_clause cl = Disj (map convert_literal cl)"

fun convert_clause_inv :: "QBF \<Rightarrow> clause option" where
"convert_clause_inv (Disj list) = sequence (map convert_literal_inv list)" |
"convert_clause_inv _ = None"

lemma clause_inv: "convert_clause_inv (convert_clause cl) = Some cl"
proof -
  let ?list = "map convert_literal_inv (map convert_literal cl)"
  have "\<forall>x \<in> set cl. convert_literal_inv (convert_literal x) = Some x" using literal_inv by simp
  hence "map Some cl = ?list" using list_no_None_ex_list_map_Some by fastforce
  hence "sequence ?list = Some cl" using sequence_content by metis
  thus "convert_clause_inv (convert_clause cl) = Some cl" by simp
qed

(* Convert matrix *)
fun convert_matrix :: "matrix \<Rightarrow> QBF" where
"convert_matrix matrix = Conj (map convert_clause matrix)"

fun convert_matrix_inv :: "QBF \<Rightarrow> matrix option" where
"convert_matrix_inv (Conj list) = sequence (map convert_clause_inv list)" |
"convert_matrix_inv _ = None"

lemma matrix_inv: "convert_matrix_inv (convert_matrix mat) = Some mat"
proof -
  let ?list = "map convert_clause_inv (map convert_clause mat)"
  have "\<forall>x \<in> set mat. convert_clause_inv (convert_clause x) = Some x" using clause_inv by simp
  hence "map Some mat = ?list" using list_no_None_ex_list_map_Some by fastforce
  hence "sequence ?list = Some mat" using sequence_content by metis
  thus "convert_matrix_inv (convert_matrix mat) = Some mat" by simp
qed

(* Convert prefix *)
(* Length of quantifier set, used to show termination of convert. *)
fun q_length :: "'a \<times> 'a list \<Rightarrow> nat" where
"q_length (x, xs) = 1 + length xs"

(* Measure length of all quantifier sets in prefix, used to show termination of convert. *)
fun measure_prefix_length :: "pcnf \<Rightarrow> nat" where
"measure_prefix_length (Empty, _) = 0" |
"measure_prefix_length (UniversalFirst q qs, _) = q_length q + sum_list (map q_length qs)" |
"measure_prefix_length (ExistentialFirst q qs, _) = q_length q + sum_list (map q_length qs)"

(* Convert a pcnf formula to a QBF formula. A left-inverse exists, see theorem convert_inv. *)
function convert :: "pcnf \<Rightarrow> QBF" where
"convert (Empty, matrix) = convert_matrix matrix" |
"convert (UniversalFirst (x, []) [], matrix) = All x (convert (Empty, matrix))" |
"convert (ExistentialFirst (x, []) [], matrix) = Ex x (convert (Empty, matrix))" |
"convert (UniversalFirst (x, []) (q # qs), matrix) =
  All x (convert (ExistentialFirst q qs, matrix))" |
"convert (ExistentialFirst (x, []) (q # qs), matrix) =
  Ex x (convert (UniversalFirst q qs, matrix))" |
"convert (UniversalFirst (x, y # ys) qs, matrix) =
  All x (convert (UniversalFirst (y, ys) qs, matrix))" |
"convert (ExistentialFirst (x, y # ys) qs, matrix) =
  Ex x (convert (ExistentialFirst (y, ys) qs, matrix))"
  by pat_completeness auto
termination
  by (relation "measure measure_prefix_length") auto

(* Add universal quantifier to front of pcnf formula. *)
fun add_universal_to_front :: "nat \<Rightarrow> pcnf \<Rightarrow> pcnf" where
"add_universal_to_front x (Empty, matrix) = (UniversalFirst (x, []) [], matrix)" |
"add_universal_to_front x (UniversalFirst (y, ys) qs, matrix) =
  (UniversalFirst (x, y # ys) qs, matrix)" |
"add_universal_to_front x (ExistentialFirst (y, ys) qs, matrix) =
  (UniversalFirst (x, []) ((y, ys) # qs), matrix)"

(* Add existential quantifier to front of pcnf formula. *)
fun add_existential_to_front :: "nat \<Rightarrow> pcnf \<Rightarrow> pcnf" where
"add_existential_to_front x (Empty, matrix) = (ExistentialFirst (x, []) [], matrix)" |
"add_existential_to_front x (ExistentialFirst (y, ys) qs, matrix) =
  (ExistentialFirst (x, y # ys) qs, matrix)" |
"add_existential_to_front x (UniversalFirst (y, ys) qs, matrix) =
  (ExistentialFirst (x, []) ((y, ys) # qs), matrix)"

(* Left-inverse for convert, see theorem convert_inv. *)
fun convert_inv :: "QBF \<Rightarrow> pcnf option" where
"convert_inv (All x qbf) = map_option (\<lambda>p. add_universal_to_front x p) (convert_inv qbf)" |
"convert_inv (Ex x qbf) = map_option (\<lambda>p. add_existential_to_front x p) (convert_inv qbf)" |
"convert_inv qbf = map_option (\<lambda>m. (Empty, m)) (convert_matrix_inv qbf)"

lemma convert_add_all: "convert (add_universal_to_front x pcnf) = All x (convert pcnf)"
  by (induction rule: add_universal_to_front.induct) auto

lemma convert_add_ex: "convert (add_existential_to_front x pcnf) = Ex x (convert pcnf)"
  by (induction rule: add_existential_to_front.induct) auto

(*
(* Lemmas that are not needed at the moment *)
lemma add_all_inv:
  assumes "convert_inv (convert pcnf) = Some pcnf"
  shows "convert_inv (convert (add_universal_to_front x pcnf))
        = Some (add_universal_to_front x pcnf)"
  using assms convert_add_all by simp

lemma add_ex_inv:
  assumes "convert_inv (convert pcnf) = Some pcnf"
  shows "convert_inv (convert (add_existential_to_front x pcnf))
        = Some (add_existential_to_front x pcnf)"
  using assms convert_add_ex by simp
*)

(* convert_inv is a left-inverse of convert *)
theorem convert_inv: "convert_inv (convert pcnf) = Some pcnf"
proof (induction pcnf)
  case (Pair prefix matrix)
  show "convert_inv (convert (prefix, matrix)) = Some (prefix, matrix)"
    using matrix_inv by (induction rule: convert.induct) auto
qed

(* Corollary: convert is injective. *)
theorem convert_injective: "inj convert"
  apply (rule inj_on_inverseI[where ?g = "the \<circ> convert_inv"])
  by (simp add: convert_inv)

(*** Predicates ***)
(* Is the QBF a literal? *)
fun literal_p :: "QBF \<Rightarrow> bool" where
"literal_p (Var _) = True" |
"literal_p (Neg (Var _)) = True" |
"literal_p _ = False"

(* Is the QBF a clause? *)
fun clause_p :: "QBF \<Rightarrow> bool" where
"clause_p (Disj list) = list_all literal_p list" |
"clause_p _ = False"

(* Is the QBF in conjunctive normal form? *)
fun cnf_p :: "QBF \<Rightarrow> bool" where
"cnf_p (Conj list) = list_all clause_p list" |
"cnf_p _ = False"

(* Is the QBF in prenex normal form with a conjunctive normal form matrix? *)
fun pcnf_p :: "QBF \<Rightarrow> bool" where
"pcnf_p (Ex _ qbf) = pcnf_p qbf" |
"pcnf_p (All _ qbf) = pcnf_p qbf" |
"pcnf_p (Conj list) = cnf_p (Conj list)" |
"pcnf_p _ = False"

(*** Proofs that predicates hold after conversion. ***)
lemma convert_literal_p: "literal_p (convert_literal lit)"
  by (cases lit) auto

lemma convert_clause_p: "clause_p (convert_clause cl)"
  using convert_literal_p by (induction cl) auto

lemma convert_cnf_p: "cnf_p (convert_matrix mat)"
  using convert_clause_p by (induction mat) auto

theorem convert_pcnf_p: "pcnf_p (convert pcnf)"
  using convert_cnf_p by (induction rule: convert.induct) auto

(*** Proofs that there is a pcnf formula yielding any pcnf_p QBF formula ***)
lemma convert_literal_p_ex:
  assumes "literal_p lit"
  shows "\<exists>l. convert_literal l = lit"
proof -
  have "\<exists>l. convert_literal l = Var x" for x using convert_literal.simps by blast
  moreover have "\<exists>l. convert_literal l = Neg (Var x)" for x using convert_literal.simps by blast
  ultimately show "\<exists>l. convert_literal l = lit"
    using assms by (induction rule: literal_p.induct) auto
qed

lemma convert_clause_p_ex:
  assumes "clause_p cl"
  shows "\<exists>c. convert_clause c = cl"
proof -
  from assms obtain xs where 0: "Disj xs = cl" by (metis clause_p.elims(2))
  hence "list_all literal_p xs" using assms by fastforce  
  hence "\<exists>ys. map convert_literal ys = xs" using convert_literal_p_ex
  proof (induction xs)
    case Nil
    show "\<exists>ys. map convert_literal ys = []" by simp
  next
    case (Cons x xs)
    from this obtain ys where "map convert_literal ys = xs" by fastforce
    moreover from Cons obtain y where "convert_literal y = x" by fastforce
    ultimately have "map convert_literal (y # ys) = x # xs" by simp
    thus "\<exists>ys. map convert_literal ys = x # xs" by (rule exI)
  qed
  thus "\<exists>c. convert_clause c = cl" using 0 by fastforce
qed

lemma convert_cnf_p_ex:
  assumes "cnf_p mat"
  shows "\<exists>m. convert_matrix m = mat"
proof -
  from assms obtain xs where 0: "Conj xs = mat" by (metis cnf_p.elims(2))
  hence "list_all clause_p xs" using assms by fastforce
  hence "\<exists>ys. map convert_clause ys = xs" using convert_clause_p_ex
  proof (induction xs)
    case Nil
    show "\<exists>ys. map convert_clause ys = []" by simp
  next
    case (Cons x xs)
    from this obtain ys where "map convert_clause ys = xs" by fastforce
    moreover from Cons obtain y where "convert_clause y = x" by fastforce
    ultimately have "map convert_clause (y # ys) = x # xs" by simp
    thus "\<exists>ys. map convert_clause ys = x # xs" by (rule exI)
  qed
  thus "\<exists>m. convert_matrix m = mat" using 0 by fastforce
qed

theorem convert_pcnf_p_ex:
  assumes "pcnf_p qbf"
  shows "\<exists>pcnf. convert pcnf = qbf" using assms
proof (induction qbf)
  case (Var x)
  hence False by simp
  thus ?case by simp
next
  case (Neg qbf)
  hence False by simp
  thus ?case by simp
next
  case (Conj x)
  hence "cnf_p (Conj x)" by simp
  from this obtain m where "convert_matrix m = Conj x" using convert_cnf_p_ex by blast
  hence "convert (Empty, m) = Conj x" by simp
  thus "\<exists>pcnf. convert pcnf = Conj x" by (rule exI)
next
  case (Disj x)
  hence False by simp
  thus ?case by simp
next
  case (Ex x1a qbf)
  from this obtain pcnf where "convert pcnf = qbf" by fastforce
  hence "convert (add_existential_to_front x1a pcnf) = Ex x1a qbf" using convert_add_ex by simp
  thus "\<exists>pcnf. convert pcnf = QBF.Ex x1a qbf" by (rule exI)
next
  case (All x1a qbf)
  from this obtain pcnf where "convert pcnf = qbf" by fastforce
  hence "convert (add_universal_to_front x1a pcnf) = All x1a qbf" using convert_add_all by simp
  thus "\<exists>pcnf. convert pcnf = QBF.All x1a qbf" by (rule exI)
qed

(* range of convert *)
theorem convert_range: "range convert = {p. pcnf_p p}"
  using convert_pcnf_p convert_pcnf_p_ex by blast

(* convert bijective on pcnf_p subset of QBF *)
theorem convert_bijective_on: "bij_betw convert UNIV {p. pcnf_p p}"
  by (simp add: bij_betw_def convert_injective convert_range)

(*** Free Variables ***)
fun free_variables_aux :: "nat set \<Rightarrow> QBF \<Rightarrow> nat list" where
"free_variables_aux bound (Var x) = (if x \<in> bound then [] else [x])" |
"free_variables_aux bound (Neg qbf) = free_variables_aux bound qbf" |
"free_variables_aux bound (Conj list) = concat (map (free_variables_aux bound) list)" |
"free_variables_aux bound (Disj list) = concat (map (free_variables_aux bound) list)" |
"free_variables_aux bound (Ex x qbf) = free_variables_aux (insert x bound) qbf" |
"free_variables_aux bound (All x qbf) = free_variables_aux (insert x bound) qbf"

fun free_variables :: "QBF \<Rightarrow> nat list" where
"free_variables qbf = sort (remdups (free_variables_aux {} qbf))"

lemma bound_subtract_equiv:
  "set (free_variables_aux (bound \<union> new) qbf) = set (free_variables_aux bound qbf) - new"
  by (induction bound qbf rule: free_variables_aux.induct) auto

(*** Existential Closure ***)
fun existential_closure_aux :: "QBF \<Rightarrow> nat list \<Rightarrow> QBF" where
"existential_closure_aux qbf Nil = qbf" |
"existential_closure_aux qbf (Cons x xs) = Ex x (existential_closure_aux qbf xs)"

fun existential_closure :: "QBF \<Rightarrow> QBF" where
"existential_closure qbf = existential_closure_aux qbf (free_variables qbf)"

lemma ex_closure_aux_vars_not_free:
  "set (free_variables (existential_closure_aux qbf vars)) = set (free_variables qbf) - set vars"
proof (induction vars)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  thus ?case using bound_subtract_equiv[of "{}" "{x}"] by auto
qed

theorem ex_closure_no_free: "set (free_variables (existential_closure qbf)) = {}"
  using ex_closure_aux_vars_not_free by simp

lemma swap_substitute_var_order:
  assumes "x1 \<noteq> x2 \<or> b1 = b2"
  shows "substitute_var x1 b1 (substitute_var x2 b2 qbf)
        = substitute_var x2 b2 (substitute_var x1 b1 qbf)"
proof (induction qbf)
  case (Var x)
  show ?case
  proof (cases b2)
    case True
    then show ?thesis using assms by (cases b1) auto
  next
    case False
    then show ?thesis using assms by (cases b1) auto
  qed
next
  case (Neg qbf)
  then show ?case by simp
next
  case (Conj x)
  then show ?case by simp
next
  case (Disj x)
  then show ?case by simp
next
  case (Ex x1a qbf)
  then show ?case by simp
next
  case (All x1a qbf)
  then show ?case by simp
qed

lemma remove_outer_substitute_var:
  assumes "x1 = x2"
  shows "substitute_var x1 b1 (substitute_var x2 b2 qbf) = (substitute_var x2 b2 qbf)" using assms
proof (induction qbf)
  case (Var x)
  show ?case
  proof (cases b2)
    case True
    then show ?thesis using assms by (cases b1) auto
  next
    case False
    then show ?thesis using assms by (cases b1) auto
  qed
next
  case (Neg qbf)
  thus ?case by simp
next
  case (Conj x)
  thus ?case by simp
next
  case (Disj x)
  thus ?case by simp
next
  case (Ex x1a qbf)
  thus ?case by simp
next
  case (All x1a qbf)
  thus ?case by simp
qed

lemma qbf_semantics_substitute_eq_assign:
  "qbf_semantics I (substitute_var x b qbf) \<longleftrightarrow> qbf_semantics (I(x := b)) qbf"
proof (induction "I(x := b)" qbf rule: qbf_semantics.induct)
  case (1 z)
  then show ?case by (cases b) auto
next
  case (2 qbf)
  then show ?case by simp
next
  case (3 qbf_list)
  then show ?case by (induction qbf_list) auto
next
  case (4 qbf_list)
  then show ?case by (induction qbf_list) auto
next
  case (5 x' qbf)
  thus ?case by (cases "x' = x")
                (auto simp add: swap_substitute_var_order remove_outer_substitute_var)
next
  case (6 x' qbf)
  thus ?case by (cases "x' = x")
                (auto simp add: swap_substitute_var_order remove_outer_substitute_var)
qed

lemma sat_iff_ex_sat: "satisfiable qbf \<longleftrightarrow> satisfiable (Ex x qbf)"
proof (cases "satisfiable qbf")
  case True
  from this obtain I where I_def: "qbf_semantics I qbf" unfolding satisfiable_def by blast
  have "I(x := I x) = I(x := True) \<or> I(x := I x) = I(x := False)" by (cases "I x") auto
  hence "I = I(x := True) \<or> I = I(x := False)" by simp
  hence "qbf_semantics (I(x := True)) qbf \<or> qbf_semantics (I(x := False)) qbf"
    using I_def by fastforce
  moreover have "satisfiable (Ex x qbf)
                = (\<exists>I. qbf_semantics (I(x := True)) qbf
                  \<or> qbf_semantics (I(x := False)) qbf)"
    by (simp add: satisfiable_def qbf_semantics_substitute_eq_assign)
  ultimately have "satisfiable (QBF.Ex x qbf)" by blast
  thus ?thesis using True by simp
next
  case False
  thus ?thesis unfolding satisfiable_def using qbf_semantics_substitute_eq_assign by simp
qed

lemma sat_iff_ex_close_aux_sat: "satisfiable qbf \<longleftrightarrow> satisfiable (existential_closure_aux qbf vars)"
  using sat_iff_ex_sat by (induction vars) auto

theorem sat_iff_ex_close_sat: "satisfiable qbf \<longleftrightarrow> satisfiable (existential_closure qbf)"
  using sat_iff_ex_close_aux_sat by simp

(*** Naive solver ***)

(* quantifier expansion *)
fun list_max :: "nat list \<Rightarrow> nat" where
"list_max Nil = 0" |
"list_max (Cons x xs) = max x (list_max xs)"

fun qbf_quantifier_depth :: "QBF \<Rightarrow> nat" where
"qbf_quantifier_depth (Var x) = 0" |
"qbf_quantifier_depth (Neg qbf) = qbf_quantifier_depth qbf" |
"qbf_quantifier_depth (Conj list) = list_max (map qbf_quantifier_depth list)" |
"qbf_quantifier_depth (Disj list) = list_max (map qbf_quantifier_depth list)" |
"qbf_quantifier_depth (Ex x qbf) = 1 + (qbf_quantifier_depth qbf)" |
"qbf_quantifier_depth (All x qbf) = 1 + (qbf_quantifier_depth qbf)"

lemma qbf_quantifier_depth_substitute:
  "qbf_quantifier_depth (substitute_var z b qbf) = qbf_quantifier_depth qbf"
proof (induction qbf)
  case (Var x)
  show ?case by (cases b) auto
next
  case (Neg qbf)
  thus ?case by simp
next
  case (Conj xs)
  thus ?case by (induction xs) auto
next
  case (Disj xs)
  thus ?case by (induction xs) auto
next
  case (Ex x1a qbf)
  thus ?case by simp
next
  case (All x1a qbf)
  thus ?case by simp
qed

lemma qbf_quantifier_depth_eq_max:
  assumes "\<not>qbf_quantifier_depth z < list_max (map qbf_quantifier_depth qbf_list)"
  and "z \<in> set qbf_list"
  shows "qbf_quantifier_depth z = list_max (map qbf_quantifier_depth qbf_list)" using assms
proof (induction qbf_list)
  case Nil
  hence False by simp
  thus ?case by simp
next
  case (Cons x xs)
  thus "qbf_quantifier_depth z = list_max (map qbf_quantifier_depth (x # xs))"
    by (cases "x = z") auto
qed

function expand_quantifiers :: "QBF \<Rightarrow> QBF" where
"expand_quantifiers (Var x) = (Var x)" |
"expand_quantifiers (Neg qbf) = Neg (expand_quantifiers qbf)" |
"expand_quantifiers (Conj list) = Conj (map expand_quantifiers list)" |
"expand_quantifiers (Disj list) = Disj (map expand_quantifiers list)" |
"expand_quantifiers (Ex x qbf) = (Disj [substitute_var x True (expand_quantifiers qbf),
                                        substitute_var x False (expand_quantifiers qbf)])" |
"expand_quantifiers (All x qbf) = (Conj [substitute_var x True (expand_quantifiers qbf),
                                         substitute_var x False (expand_quantifiers qbf)])"
  by pat_completeness auto
termination
  apply (relation "measures [qbf_quantifier_depth, qbf_measure]")
  by (auto simp add: qbf_quantifier_depth_substitute qbf_quantifier_depth_eq_max)
     (auto simp add: qbf_measure_lt_sum_list)

(* Property 1: no quantifiers after expansion. *)
lemma no_quants_after_expand_quants: "qbf_quantifier_depth (expand_quantifiers qbf) = 0"
proof (induction qbf)
  case (Var x)
  show ?case by simp
next
  case (Neg qbf)
  thus ?case by simp
next
  case (Conj x)
  thus ?case by (induction x) auto
next
  case (Disj x)
  thus ?case by (induction x) auto
next
  case (Ex x1a qbf)
  thus ?case using qbf_quantifier_depth_substitute Ex.IH by simp
next
  case (All x1a qbf)
  thus ?case using qbf_quantifier_depth_substitute All.IH by simp
qed

(* Property 2: semantics invariant under expansion (logical equivalence). *)

lemma semantics_inv_under_expand:
  "qbf_semantics I qbf = qbf_semantics I (expand_quantifiers qbf)"
proof (induction qbf arbitrary: I)
  case (Var x)
  show ?case by force
next
  case (Neg qbf)
  thus ?case by simp
next
  case (Conj x)
  thus ?case by (induction x) auto
next
  case (Disj x)
  thus ?case by (induction x) auto
next
  case (Ex x1a qbf)
  thus "qbf_semantics I (QBF.Ex x1a qbf) = qbf_semantics I (expand_quantifiers (QBF.Ex x1a qbf))"
    using qbf_semantics_substitute_eq_assign by fastforce
next
  case (All x1a qbf)
  thus "qbf_semantics I (QBF.All x1a qbf) = qbf_semantics I (expand_quantifiers (QBF.All x1a qbf))"
    using qbf_semantics_substitute_eq_assign by fastforce
qed

lemma sat_iff_expand_quants_sat: "satisfiable qbf \<longleftrightarrow> satisfiable (expand_quantifiers qbf)"
  unfolding satisfiable_def using semantics_inv_under_expand by simp

(* Property 3: free variables invariant under expansion. *)
lemma set_free_vars_subst_all_eq:
  "set (free_variables (substitute_var x b qbf)) = set (free_variables (All x qbf))"
proof (induction x b qbf rule: substitute_var.induct)
  case (1 z z')
  then show ?case by simp
next
  case (2 z z')
  then show ?case by simp
next
  case (3 z b qbf)
  then show ?case by simp
next
  case (4 z b qbf_list)
  then show ?case by simp
next
  case (5 z b qbf_list)
  then show ?case by simp
next
  case (6 z b x qbf)
  then show ?case
  proof (cases "x = z")
    case True
    thus ?thesis by simp
  next
    case False
    hence "set (free_variables (substitute_var z b (QBF.Ex x qbf)))
                   = set (free_variables (substitute_var z b qbf)) - {x}"
      using bound_subtract_equiv[where ?new = "{x}"] by simp
    also have "... = set (free_variables (QBF.All z qbf)) - {x}" using 6 False by simp
    also have "... = set (free_variables_aux {x, z} qbf)"
      using bound_subtract_equiv[where ?new = "{x}"] by simp
    also have "... = set (free_variables (QBF.All z (QBF.Ex x qbf)))" by simp
    finally show ?thesis .
  qed
next
  case (7 z b y qbf)
  thus ?case
  proof (cases "y = z")
    case True
    thus ?thesis by simp
  next
    case False (* Similar to case "6, False" *)
    thus ?thesis using 7 bound_subtract_equiv[where ?new = "{y}"] by simp
  qed
qed

lemma set_free_vars_subst_ex_eq:
  "set (free_variables (substitute_var x b qbf)) = set (free_variables (Ex x qbf))"
proof (induction x b qbf rule: substitute_var.induct)
  case (1 z z')
  then show ?case by simp
next
  case (2 z z')
  then show ?case by simp
next
  case (3 z b qbf)
  then show ?case by simp
next
  case (4 z b qbf_list)
  then show ?case by simp
next
  case (5 z b qbf_list)
  then show ?case by simp
next
  case (6 z b x qbf)
  then show ?case
  proof (cases "x = z")
    case True
    thus ?thesis by simp
  next
    case False (* Similar to proof in set_free_vars_subst_all_eq *) 
    thus ?thesis using 6 bound_subtract_equiv[where ?new = "{x}"] by simp
  qed
next
  case (7 z b y qbf)
  thus ?case
  proof (cases "y = z")
    case True
    thus ?thesis by simp
  next
    case False (* Similar to proof in set_free_vars_subst_all_eq *)
    thus ?thesis using 7 bound_subtract_equiv[where ?new = "{y}"] by simp
  qed
qed

lemma free_vars_inv_under_expand_quants:
  "set (free_variables (expand_quantifiers qbf)) = set (free_variables qbf)"
proof (induction qbf)
  case (Var x)
  then show ?case by simp
next
  case (Neg qbf)
  then show ?case by simp
next
  case (Conj x)
  then show ?case by fastforce
next
  case (Disj x)
  then show ?case by fastforce
next
  case (Ex x1a qbf)
  have "set (free_variables (expand_quantifiers (QBF.Ex x1a qbf)))
                 = set (free_variables_aux {x1a} (expand_quantifiers qbf))"
    using set_free_vars_subst_ex_eq by simp
  also have "... = set (free_variables (expand_quantifiers qbf)) - {x1a}"
    using bound_subtract_equiv[where ?new = "{x1a}"] by simp
  also have "... = set (free_variables qbf) - {x1a}" using Ex.IH by simp
  also have "... = set (free_variables_aux {x1a} qbf)"
    using bound_subtract_equiv[where ?new = "{x1a}"] by simp
  also have "... = set (free_variables (QBF.Ex x1a qbf))" by simp
  finally show ?case .
next
  case (All x1a qbf) (* Similar to above *)
  thus ?case using bound_subtract_equiv[where ?new = "{x1a}"] set_free_vars_subst_all_eq by simp
qed

(* Any formula can be expanded to one with the three properties. *)
fun expand_qbf :: "QBF \<Rightarrow> QBF" where
"expand_qbf qbf = expand_quantifiers (existential_closure qbf)"

(* The important properties from the existential closure and quantifier expansion are preserved. *)
lemma sat_iff_expand_qbf_sat: "satisfiable (expand_qbf qbf) \<longleftrightarrow> satisfiable qbf"
  using sat_iff_ex_close_sat sat_iff_expand_quants_sat by simp

lemma expand_qbf_no_free: "set (free_variables (expand_qbf qbf)) = {}"
proof -
  have "set (free_variables (expand_qbf qbf)) = set (free_variables (existential_closure qbf))"
    using free_vars_inv_under_expand_quants by simp
  thus ?thesis using ex_closure_no_free by metis
qed

lemma expand_qbf_no_quants: "qbf_quantifier_depth (expand_qbf qbf) = 0"
  using no_quants_after_expand_quants by simp

(* All qbfs without any quantifiers or free variables can be evaluated. *)
fun eval_qbf :: "QBF \<Rightarrow> bool option" where
"eval_qbf (Var x) = None" |
"eval_qbf (Neg qbf) = map_option (\<lambda>x. \<not>x) (eval_qbf qbf)" |
"eval_qbf (Conj list) = map_option (list_all id) (sequence (map eval_qbf list))" |
"eval_qbf (Disj list) = map_option (list_ex id) (sequence (map eval_qbf list))" |
"eval_qbf (Ex x qbf) = None" |
"eval_qbf (All x qbf) = None"

lemma pred_map_ex: "list_ex Q (map f x) = list_ex (Q \<circ> f) x"
  by (induction x) auto

(* The evaluation implements the semantics. *)
lemma eval_qbf_implements_semantics:
  assumes "set (free_variables qbf) = {}" and "qbf_quantifier_depth qbf = 0"
  shows "eval_qbf qbf = Some (qbf_semantics I qbf)" using assms
proof (induction qbf)
  case (Var x)
  then show ?case by simp
next
  case (Neg qbf)
  then show ?case by simp
next
  case (Conj x)
  hence "\<forall>q \<in> set x. eval_qbf q = Some (qbf_semantics I q)" by (induction x) auto
  thus "eval_qbf (Conj x) = Some (qbf_semantics I (Conj x))"
  proof (induction x)
    case Nil
    show "eval_qbf (Conj []) = Some (qbf_semantics I (Conj []))" by simp
  next
    case (Cons y ys)
    have "map eval_qbf ys = map Some (map (qbf_semantics I) ys)" using Cons by simp
    moreover have "eval_qbf y = Some (qbf_semantics I y)" using Cons.prems by simp
    ultimately have "map eval_qbf (y # ys) = map Some (map (qbf_semantics I) (y # ys))" by simp
    hence "sequence (map eval_qbf (y # ys)) = Some (map (qbf_semantics I) (y # ys))"
      using sequence_content by metis
    hence "eval_qbf (Conj (y # ys))
          = Some (list_all id (map (qbf_semantics I) (y # ys)))"
      by simp
    hence "eval_qbf (Conj (y # ys)) = Some (list_all (qbf_semantics I) (y # ys))"
      by (simp add: fun.map_ident list.pred_map)
    thus "eval_qbf (Conj (y # ys)) = Some (qbf_semantics I (Conj (y # ys)))" by simp
  qed
next
  case (Disj x) (* Similar to previous case *)
  hence "\<forall>q \<in> set x. eval_qbf q = Some (qbf_semantics I q)" by (induction x) auto
  thus "eval_qbf (Disj x) = Some (qbf_semantics I (Disj x))"
  proof (induction x)
    case Nil
    show "eval_qbf (Disj []) = Some (qbf_semantics I (Disj []))" by simp
  next
    case (Cons y ys)
    have "map eval_qbf ys = map Some (map (qbf_semantics I) ys)" using Cons by simp
    moreover have "eval_qbf y = Some (qbf_semantics I y)" using Cons.prems by simp
    ultimately have "map eval_qbf (y # ys) = map Some (map (qbf_semantics I) (y # ys))" by simp
    hence "sequence (map eval_qbf (y # ys)) = Some (map (qbf_semantics I) (y # ys))"
      using sequence_content by metis
    hence "eval_qbf (Disj (y # ys))
          = Some (list_ex id (map (qbf_semantics I) (y # ys)))"
      by simp
    hence "eval_qbf (Disj (y # ys)) = Some (list_ex (qbf_semantics I) (y # ys))"
      by (simp add: fun.map_ident pred_map_ex)
    thus "eval_qbf (Disj (y # ys)) = Some (qbf_semantics I (Disj (y # ys)))" by simp
  qed
next
  case (Ex x1a qbf)
  hence False by simp
  thus ?case by simp
next
  case (All x1a qbf)
  hence False by simp
  thus ?case by simp
qed

(* This can then be used to implement the naive solver ... *)
fun naive_solver :: "QBF \<Rightarrow> bool" where
"naive_solver qbf = the (eval_qbf (expand_qbf qbf))"

(* ...which is correct. *)
theorem naive_solver_correct: "naive_solver qbf \<longleftrightarrow> satisfiable qbf"
proof -
  have "\<forall>I. naive_solver qbf = the (Some (qbf_semantics I (expand_qbf qbf)))"
    using expand_qbf_no_free expand_qbf_no_quants eval_qbf_implements_semantics by simp
  hence "naive_solver qbf = satisfiable (expand_qbf qbf)" unfolding satisfiable_def by simp
  thus "naive_solver qbf = satisfiable qbf" using sat_iff_expand_qbf_sat by simp
qed

value test_qbf
value "existential_closure test_qbf"
value "expand_qbf test_qbf"
value "naive_solver test_qbf"
value "the (convert_inv test_qbf)"
value "the (convert_inv (existential_closure test_qbf))"
value "convert_inv (expand_qbf test_qbf)"

(* Formalisation of pcnf assignment *)
fun lit_neg :: "literal \<Rightarrow> literal" where
"lit_neg (P l) = N l" |
"lit_neg (N l) = P l"

fun lit_var :: "literal \<Rightarrow> nat" where
"lit_var (P l) = l" |
"lit_var (N l) = l"

fun remove_lit_neg :: "literal \<Rightarrow> clause \<Rightarrow> clause" where
"remove_lit_neg lit clause = filter (\<lambda>l. l \<noteq> lit_neg lit) clause"

fun remove_lit_clauses :: "literal \<Rightarrow> matrix \<Rightarrow> matrix" where
"remove_lit_clauses lit matrix = filter (\<lambda>cl. \<not>(list_ex (\<lambda>l. l = lit) cl)) matrix"

fun matrix_assign :: "literal \<Rightarrow> matrix \<Rightarrow> matrix" where
"matrix_assign lit matrix = remove_lit_clauses lit (map (remove_lit_neg lit) matrix)"

fun prefix_pop :: "prefix \<Rightarrow> prefix" where
"prefix_pop Empty = Empty" |
"prefix_pop (UniversalFirst (x, Nil) Nil) = Empty" |
"prefix_pop (UniversalFirst (x, Nil) (Cons (y, ys) qs)) = ExistentialFirst (y, ys) qs" |
"prefix_pop (UniversalFirst (x, (Cons xx xs)) qs) = UniversalFirst (xx, xs) qs"  |
"prefix_pop (ExistentialFirst (x, Nil) Nil) = Empty" |
"prefix_pop (ExistentialFirst (x, Nil) (Cons (y, ys) qs)) = UniversalFirst (y, ys) qs" |
"prefix_pop (ExistentialFirst (x, (Cons xx xs)) qs) = ExistentialFirst (xx, xs) qs"

fun add_universal_to_prefix :: "nat \<Rightarrow> prefix \<Rightarrow> prefix" where
"add_universal_to_prefix x Empty = UniversalFirst (x, []) []" |
"add_universal_to_prefix x (UniversalFirst (y, ys) qs) =
  UniversalFirst (x, y # ys) qs" |
"add_universal_to_prefix x (ExistentialFirst (y, ys) qs) =
  UniversalFirst (x, []) ((y, ys) # qs)"

fun add_existential_to_prefix :: "nat \<Rightarrow> prefix \<Rightarrow> prefix" where
"add_existential_to_prefix x Empty = ExistentialFirst (x, []) []" |
"add_existential_to_prefix x (ExistentialFirst (y, ys) qs) =
  ExistentialFirst (x, y # ys) qs" |
"add_existential_to_prefix x (UniversalFirst (y, ys) qs) =
  ExistentialFirst (x, []) ((y, ys) # qs)"

fun quant_sets_measure :: "quant_sets \<Rightarrow> nat" where
"quant_sets_measure Nil = 0" |
"quant_sets_measure (Cons (x, xs) qs) = 1 + length xs + quant_sets_measure qs"

fun prefix_measure :: "prefix \<Rightarrow> nat" where
"prefix_measure Empty = 0" |
"prefix_measure (UniversalFirst q qs) = quant_sets_measure (Cons q qs)" |
"prefix_measure (ExistentialFirst q qs) = quant_sets_measure (Cons q qs)"

lemma prefix_pop_decreases_measure:
  "prefix \<noteq> Empty \<Longrightarrow> prefix_measure (prefix_pop prefix) < prefix_measure prefix"
  by (induction rule: prefix_pop.induct) auto

function remove_var_prefix :: "nat \<Rightarrow> prefix \<Rightarrow> prefix" where
"remove_var_prefix x Empty = Empty" |
"remove_var_prefix x (UniversalFirst (y, ys) qs) = (if x = y
  then remove_var_prefix x (prefix_pop (UniversalFirst (y, ys) qs))
  else add_universal_to_prefix y (remove_var_prefix x (prefix_pop (UniversalFirst (y, ys) qs))))" |
"remove_var_prefix x (ExistentialFirst (y, ys) qs) = (if x = y
  then remove_var_prefix x (prefix_pop (ExistentialFirst (y, ys) qs))
  else add_existential_to_prefix y (remove_var_prefix x (prefix_pop (ExistentialFirst (y, ys) qs))))"
  by pat_completeness auto
termination
  by (relation "measure (\<lambda>(x, pre). prefix_measure pre)")
     (auto simp add: prefix_pop_decreases_measure simp del: prefix_measure.simps)

fun pcnf_assign :: "literal \<Rightarrow> pcnf \<Rightarrow> pcnf" where
"pcnf_assign lit (prefix, matrix) =
  (remove_var_prefix (lit_var lit) prefix, matrix_assign lit matrix)"

value "the (convert_inv test_qbf)"
value "pcnf_assign (P 1) (the (convert_inv test_qbf))"
value "pcnf_assign (P 3) (the (convert_inv test_qbf))"

(* Formalisation of qbf variables *)
fun variables_aux :: "QBF \<Rightarrow> nat list" where
"variables_aux (Var x) = [x]" |
"variables_aux (Neg qbf) = variables_aux qbf" |
"variables_aux (Conj list) = concat (map variables_aux list)" |
"variables_aux (Disj list) = concat (map variables_aux list)" |
"variables_aux (Ex x qbf) = variables_aux qbf" |
"variables_aux (All x qbf) = variables_aux qbf"

fun variables :: "QBF \<Rightarrow> nat list" where
"variables qbf = sort (remdups (variables_aux qbf))"

fun prefix_variables_aux :: "QBF \<Rightarrow> nat list" where
"prefix_variables_aux (All y qbf) = Cons y (prefix_variables_aux qbf)" |
"prefix_variables_aux (Ex x qbf) = Cons x (prefix_variables_aux qbf)" |
"prefix_variables_aux _ = Nil"

fun prefix_variables :: "QBF \<Rightarrow> nat list" where
"prefix_variables qbf = sort (remdups (prefix_variables_aux qbf))"

(* convert is left-inverse for pcnf_p QBF formulas *)
lemma convert_inv_inv:
  "pcnf_p qbf \<Longrightarrow> convert (the (convert_inv qbf)) = qbf"
  by (metis convert_inv convert_pcnf_p_ex option.sel)

(* Alternative formalisation of pcnf semantics, free variables, prefix variables,
   variables, and existential closure *)
fun pcnf_variables :: "pcnf \<Rightarrow> nat list" where
"pcnf_variables pcnf = variables (convert pcnf)"

fun pcnf_prefix_variables :: "pcnf \<Rightarrow> nat list" where
"pcnf_prefix_variables pcnf = prefix_variables (convert pcnf)"

fun pcnf_free_variables :: "pcnf \<Rightarrow> nat list" where
"pcnf_free_variables pcnf = free_variables (convert pcnf)"

fun pcnf_existential_closure :: "pcnf \<Rightarrow> pcnf" where
"pcnf_existential_closure pcnf = the (convert_inv (existential_closure (convert pcnf)))"

(* pcnf is satisfiable iff existential closure is *)
lemma ex_closure_aux_pcnf_p_inv:
  "pcnf_p qbf \<Longrightarrow> pcnf_p (existential_closure_aux qbf vars)"
  by (induction qbf vars rule: existential_closure_aux.induct) auto

lemma ex_closure_pcnf_p_inv:
  "pcnf_p qbf \<Longrightarrow> pcnf_p (existential_closure qbf)"
  using ex_closure_aux_pcnf_p_inv by simp

theorem pcnf_sat_iff_ex_close_sat:
  "satisfiable (convert pcnf) = satisfiable (convert (pcnf_existential_closure pcnf))"
  using convert_inv_inv convert_pcnf_p ex_closure_pcnf_p_inv sat_iff_ex_close_sat by auto

(* pcnf existential closure does not have any free variables *)
theorem pcnf_ex_closure_no_free:
  "pcnf_free_variables (pcnf_existential_closure pcnf) = []"
  using convert_inv_inv convert_pcnf_p ex_closure_pcnf_p_inv ex_closure_no_free by auto

(* We will show that the set of free variables is decreasing after assignment using the following
proof skeleton: *)
lemma free_assgn_proof_skeleton:
  "free = var - pre \<Longrightarrow> free_assgn = var_assgn - pre_assgn
  \<Longrightarrow> var_assgn \<subseteq> var - lit
  \<Longrightarrow> pre_assgn = pre - lit
  \<Longrightarrow> free_assgn \<subseteq> free - lit"
  by auto

(* free = vars - prefix *)
lemma lit_p_free_eq_vars:
  "literal_p qbf \<Longrightarrow> set (free_variables qbf) = set (variables qbf)"
  by (induction qbf rule: literal_p.induct) auto

lemma cl_p_free_eq_vars:
  assumes "clause_p qbf"
  shows "set (free_variables qbf) = set (variables qbf)"
proof -
  obtain qbf_list where list_def: "qbf = Disj qbf_list"
    using assms by (induction qbf rule: clause_p.induct) auto
  moreover from this have "list_all literal_p qbf_list" using assms by simp
  ultimately show ?thesis using lit_p_free_eq_vars by (induction qbf_list arbitrary: qbf) auto
qed

lemma cnf_p_free_eq_vars:
  assumes "cnf_p qbf"
  shows "set (free_variables qbf) = set (variables qbf)"
proof -
  obtain qbf_list where list_def: "qbf = Conj qbf_list"
    using assms by (induction qbf rule: cnf_p.induct) auto
  moreover from this have "list_all clause_p qbf_list" using assms by simp
  ultimately show ?thesis using cl_p_free_eq_vars by (induction qbf_list arbitrary: qbf) auto
qed

lemma pcnf_p_free_eq_vars_minus_prefix_aux:
  "pcnf_p qbf \<Longrightarrow> set (free_variables qbf) = set (variables qbf) - set (prefix_variables_aux qbf)"
proof (induction qbf rule: prefix_variables_aux.induct)
  case (1 y qbf)
  thus ?case using bound_subtract_equiv[of "{}" "{y}" qbf] by force
next
  case (2 x qbf)
  thus ?case using bound_subtract_equiv[of "{}" "{x}" qbf] by force
next
  case ("3_1" v)
  hence False by simp
  thus ?case by simp
next
  case ("3_2" v)
  hence False by simp
  thus ?case by simp
next
  case ("3_3" v)
  hence "cnf_p (Conj v)" by (induction "Conj v" rule: pcnf_p.induct) auto
  thus ?case using cnf_p_free_eq_vars by fastforce
next
  case ("3_4" v)
  hence False by simp
  thus ?case by simp
qed

lemma pcnf_p_free_eq_vars_minus_prefix:
  "pcnf_p qbf \<Longrightarrow> set (free_variables qbf) = set (variables qbf) - set (prefix_variables qbf)"
  using pcnf_p_free_eq_vars_minus_prefix_aux by simp

lemma pcnf_free_eq_vars_minus_prefix:
  "set (pcnf_free_variables pcnf)
  = set (pcnf_variables pcnf) - set (pcnf_prefix_variables pcnf)"
  using pcnf_p_free_eq_vars_minus_prefix convert_pcnf_p by simp

(* var_assgn \<subseteq> var - lit *)
lemma lit_not_in_matrix_assign_variables:
  "lit_var lit \<notin> set (variables (convert_matrix (matrix_assign lit matrix)))"
proof (induction matrix)
  case Nil
  then show ?case by simp
next
  case (Cons cl cls)
  then show ?case
  proof (induction cl)
    case Nil
    then show ?case by simp
  next
    case (Cons l ls)
    then show ?case
    proof (induction l)
      case (P x)
      then show ?case
      proof (induction lit)
        case (P x')
        then show ?case by (cases "x = x'") auto
      next
        case (N x')
        then show ?case by (cases "x = x'") auto
      qed
    next
      case (N x)
      then show ?case
      proof (induction lit)
        case (P x')
        then show ?case by (cases "x = x'") auto
      next
        case (N x')
        then show ?case by (cases "x = x'") auto
      qed
    qed
  qed
qed

lemma matrix_assign_vars_subseteq_matrix_vars_minus_lit:
  "set (variables (convert_matrix (matrix_assign lit matrix)))
  \<subseteq> set (variables (convert_matrix matrix)) - {lit_var lit}"
  using lit_not_in_matrix_assign_variables by force

lemma pcnf_vars_eq_matrix_vars:
  "set (pcnf_variables (prefix, matrix))
  = set (variables (convert_matrix matrix))"
  by (induction "(prefix, matrix)" arbitrary: prefix rule: convert.induct) auto

lemma pcnf_assign_vars_subseteq_vars_minus_lit:
  "set (pcnf_variables (pcnf_assign x pcnf))
  \<subseteq> set (pcnf_variables pcnf) - {lit_var x}"
  using matrix_assign_vars_subseteq_matrix_vars_minus_lit pcnf_vars_eq_matrix_vars
  by (induction pcnf) simp

(* prefix_assgn = prefix - lit *)
lemma add_ex_adds_prefix_var:
  "set (pcnf_prefix_variables (add_existential_to_front x pcnf))
  = set (pcnf_prefix_variables pcnf) \<union> {x}"
  using convert_add_ex bound_subtract_equiv[of "{}" "{x}" "convert pcnf"] by auto

lemma add_ex_to_prefix_eq_add_to_front:
  "(add_existential_to_prefix x prefix, matrix) = add_existential_to_front x (prefix, matrix)"
  by (induction prefix) auto

lemma add_all_adds_prefix_var:
  "set (pcnf_prefix_variables (add_universal_to_front x pcnf))
  = set (pcnf_prefix_variables pcnf) \<union> {x}"
  using convert_add_all bound_subtract_equiv[of "{}" "{x}" "convert pcnf"] by auto

lemma add_all_to_prefix_eq_add_to_front:
  "(add_universal_to_prefix x prefix, matrix) = add_universal_to_front x (prefix, matrix)"
  by (induction prefix) auto

lemma prefix_assign_vars_eq_prefix_vars_minus_lit:
  "set (pcnf_prefix_variables (remove_var_prefix x prefix, matrix))
  = set (pcnf_prefix_variables (prefix, matrix)) - {x}"
proof (induction "(prefix, matrix)" arbitrary: prefix rule: convert.induct)
  case 1
  then show ?case by simp
next
  case (2 x)
  then show ?case by simp
next
  case (3 x)
  then show ?case by simp
next
  case (4 x q qs)
  then show ?case
    using add_all_adds_prefix_var add_all_to_prefix_eq_add_to_front by (induction q) auto
next
  case (5 x q qs)
  then show ?case using add_ex_adds_prefix_var add_ex_to_prefix_eq_add_to_front by (induction q) auto
next
  case (6 x y ys qs)
  then show ?case using add_all_adds_prefix_var add_all_to_prefix_eq_add_to_front by auto
next
  case (7 x y ys qs)
  then show ?case using add_ex_adds_prefix_var add_ex_to_prefix_eq_add_to_front by auto
qed

lemma prefix_vars_matrix_inv:
  "set (pcnf_prefix_variables (prefix, matrix1))
  = set (pcnf_prefix_variables (prefix, matrix2))"
  by (induction "(prefix, matrix1)" arbitrary: prefix rule: convert.induct) auto

lemma pcnf_prefix_vars_eq_prefix_minus_lit:
  "set (pcnf_prefix_variables (pcnf_assign x pcnf))
  = set (pcnf_prefix_variables pcnf) - {lit_var x}"
  using prefix_assign_vars_eq_prefix_vars_minus_lit prefix_vars_matrix_inv
  by (induction pcnf) fastforce

(* This concludes the proof of the theorem: *)
theorem pcnf_assign_free_subseteq_free_minus_lit:
  "set (pcnf_free_variables (pcnf_assign x pcnf)) \<subseteq> set (pcnf_free_variables pcnf) - {lit_var x}"
  using free_assgn_proof_skeleton[OF
      pcnf_free_eq_vars_minus_prefix[of pcnf]
      pcnf_free_eq_vars_minus_prefix[of "pcnf_assign x pcnf"]
      pcnf_assign_vars_subseteq_vars_minus_lit[of x pcnf]
      pcnf_prefix_vars_eq_prefix_minus_lit[of x pcnf]] .

(* A pcnf with an empty matrix and no variables is true or false. *)
lemma no_vars_if_no_free_no_prefix_vars:
  "pcnf_free_variables pcnf = [] \<Longrightarrow> pcnf_prefix_variables pcnf = [] \<Longrightarrow> pcnf_variables pcnf = []"
  by (metis Diff_iff list.set_intros(1) neq_Nil_conv pcnf_free_eq_vars_minus_prefix)

lemma no_vars_if_no_free_empty_prefix:
  "pcnf_free_variables (Empty, matrix) = [] \<Longrightarrow> pcnf_variables (Empty, matrix) = []"
  using no_vars_if_no_free_no_prefix_vars by fastforce

lemma single_clause_variables:
  "set (pcnf_variables (Empty, [cl])) = set (map lit_var cl)"
proof (induction cl)
  case Nil
  then show ?case by simp
next
  case (Cons l ls)
  then show ?case by (induction l) auto
qed

lemma empty_prefix_cons_matrix_variables:
  "set (pcnf_variables (Empty, Cons cl cls))
  = set (pcnf_variables (Empty, cls)) \<union> set (map lit_var cl)"
  using single_clause_variables by auto

lemma matrix_shape_if_no_variables:
  "pcnf_variables (Empty, matrix) = [] \<Longrightarrow> (\<exists>n. matrix = replicate n [])"
proof (induction matrix)
  case Nil
  then show ?case by simp
next
  case (Cons cl cls)
  show ?case
  proof (cases "cl = Nil")
    case True
    from this obtain n where "cls = replicate n []" using Cons by fastforce
    hence "cl # cls = replicate (Suc n) []" using True by simp
    then show ?thesis by (rule exI) 
  next
    case False
    hence "set (pcnf_variables (Empty, cl # cls)) \<noteq> {}"
      using empty_prefix_cons_matrix_variables by simp
    hence False using Cons by blast
    then show ?thesis by simp
  qed
qed

(* Definition of pcnf semantics.
  This is equal to qbf semantics according to lemma qbf_semantics_eq_pcnf_semantics.
  I needed this in addition to the qbf semantics for some lemmas. *)
fun literal_semantics :: "(nat \<Rightarrow> bool) \<Rightarrow> literal \<Rightarrow> bool" where
"literal_semantics I (P x) = I x" |
"literal_semantics I (N x) = (\<not>I x)"

fun clause_semantics :: "(nat \<Rightarrow> bool) \<Rightarrow> clause \<Rightarrow> bool" where
"clause_semantics I clause = list_ex (literal_semantics I) clause"

fun matrix_semantics :: "(nat \<Rightarrow> bool) \<Rightarrow> matrix \<Rightarrow> bool" where
"matrix_semantics I matrix = list_all (clause_semantics I) matrix"

function pcnf_semantics :: "(nat \<Rightarrow> bool) \<Rightarrow> pcnf \<Rightarrow> bool" where
"pcnf_semantics I (Empty, matrix) =
  matrix_semantics I matrix" |
"pcnf_semantics I (UniversalFirst (y, []) [], matrix) =
  (pcnf_semantics (I(y := True)) (Empty, matrix)
  \<and> pcnf_semantics (I(y := False)) (Empty, matrix))" |
"pcnf_semantics I (ExistentialFirst (x, []) [], matrix) =
  (pcnf_semantics (I(x := True)) (Empty, matrix)
  \<or> pcnf_semantics (I(x := False)) (Empty, matrix))" |
"pcnf_semantics I (UniversalFirst (y, []) (q # qs), matrix) =
  (pcnf_semantics (I(y := True)) (ExistentialFirst q qs, matrix)
  \<and> pcnf_semantics (I(y := False)) (ExistentialFirst q qs, matrix))" |
"pcnf_semantics I (ExistentialFirst (x, []) (q # qs), matrix) =
  (pcnf_semantics (I(x := True)) (UniversalFirst q qs, matrix)
  \<or> pcnf_semantics (I(x := False)) (UniversalFirst q qs, matrix))" |
"pcnf_semantics I (UniversalFirst (y, yy # ys) qs, matrix) =
  (pcnf_semantics (I(y := True)) (UniversalFirst (yy, ys) qs, matrix)
  \<and> pcnf_semantics (I(y := False)) (UniversalFirst (yy, ys) qs, matrix))" |
"pcnf_semantics I (ExistentialFirst (x, xx # xs) qs, matrix) =
  (pcnf_semantics (I(x := True)) (ExistentialFirst (xx, xs) qs, matrix)
  \<or> pcnf_semantics (I(x := False)) (ExistentialFirst (xx, xs) qs, matrix))"
  by pat_completeness auto
termination
  by (relation "measure (\<lambda>(I,p). measure_prefix_length p)") auto

theorem qbf_semantics_eq_pcnf_semantics:
  "pcnf_semantics I pcnf = qbf_semantics I (convert pcnf)"
proof (induction pcnf arbitrary: I rule: convert.induct)
  case (1 matrix)
  then show ?case
  proof (induction matrix)
    case Nil
    then show ?case by simp
  next
    case (Cons cl cls)
    then show ?case
    proof (induction cl)
      case Nil
      then show ?case by simp
    next
      case (Cons l ls)
      then show ?case by (induction l) force+
    qed
  qed
next
  case (2 x matrix)
  then show ?case using convert.simps(2) pcnf_semantics.simps(2)
      qbf_semantics.simps(6) qbf_semantics_substitute_eq_assign by presburger
next
  case (3 x matrix)
  then show ?case using convert.simps(3) pcnf_semantics.simps(3)
      qbf_semantics.simps(5) qbf_semantics_substitute_eq_assign by presburger
next
  case (4 x q qs matrix)
  then show ?case using qbf_semantics_substitute_eq_assign by fastforce
next
  case (5 x q qs matrix)
  then show ?case using qbf_semantics_substitute_eq_assign by fastforce
next
  case (6 x y ys qs matrix)
  then show ?case using qbf_semantics_substitute_eq_assign by fastforce
next
  case (7 x y ys qs matrix)
  then show ?case using qbf_semantics_substitute_eq_assign by fastforce
qed

theorem qbf_semantics_eq_pcnf_semantics':
  assumes "pcnf_p qbf"
  shows "qbf_semantics I qbf = pcnf_semantics I (the (convert_inv qbf))"
  using qbf_semantics_eq_pcnf_semantics assms convert_inv_inv by simp

lemma false_if_empty_clause_in_matrix:
  "[] \<in> set matrix \<Longrightarrow> pcnf_semantics I (prefix, matrix) = False"
  by (induction I "(prefix, matrix)" arbitrary: prefix rule: pcnf_semantics.induct)
     (induction matrix, auto)

lemma true_if_matrix_empty:
  "matrix = [] \<Longrightarrow> pcnf_semantics I (prefix, matrix) = True"
  by (induction I "(prefix, matrix)" arbitrary: prefix rule: pcnf_semantics.induct) auto

lemma empty_clause_or_matrix_if_no_variables:
  "pcnf_variables (Empty, matrix) = [] \<Longrightarrow> [] \<in> set matrix \<or> matrix = []"
  using matrix_shape_if_no_variables by fastforce

(***
Start of proof showing:
\<exists>x\<Phi> \<approx>sat \<Phi>_x \<or> \<Phi>_\<not>x and \<forall>y\<Phi> \<approx>sat \<Phi>_y \<and> \<Phi>_\<not>y
if z is the first variable in the prefix.
***)

(* The clause semantics are invariant when removing false literals. *)
lemma clause_semantics_inv_remove_false:
  "clause_semantics (I(z := True)) cl = clause_semantics (I(z := True)) (remove_lit_neg (P z) cl)"
  by (induction cl) auto

lemma clause_semantics_inv_remove_true:
  "clause_semantics (I(z := False)) cl = clause_semantics (I(z := False)) (remove_lit_neg (N z) cl)"
  by (induction cl) auto

(* The matrix semantics are invariant when removing clauses containing true literals. *)
lemma matrix_semantics_inv_remove_true:
  "matrix_semantics (I(z := True)) (matrix_assign (P z) matrix)
  = matrix_semantics (I(z := True)) matrix"
proof (induction matrix)
  case Nil
  then show ?case by simp
next
  case (Cons cl cls)
  then show ?case
  proof (cases "P z \<in> set cl")
    case True
    hence 0: "clause_semantics (I(z := True)) cl" by (induction cl) auto
    have "matrix_semantics (I(z := True)) (matrix_assign (P z) (cl # cls))
         = matrix_semantics (I(z := True)) (matrix_assign (P z) cls)"
      using 0 clause_semantics_inv_remove_false by simp
    moreover have "matrix_semantics (I(z := True)) (cl # cls)
                  = matrix_semantics (I(z := True)) cls"
      using 0 by simp
    ultimately show ?thesis using Cons by blast
  next
    case False
    hence "matrix_assign (P z) (cl # cls) = remove_lit_neg (P z) cl # matrix_assign (P z) cls"
      by (induction cl) auto
    hence "matrix_semantics (I(z := True)) (matrix_assign (P z) (cl # cls))
          \<longleftrightarrow> clause_semantics (I(z := True)) (remove_lit_neg (P z) cl)
            \<and> matrix_semantics (I(z := True)) (matrix_assign (P z) cls)" by simp
    moreover have "matrix_semantics (I(z := True)) (cl # cls)
                  \<longleftrightarrow> clause_semantics (I(z := True)) cl
                    \<and> matrix_semantics (I(z := True)) cls" by simp
    ultimately show ?thesis using Cons clause_semantics_inv_remove_false by blast
  qed
qed

lemma matrix_semantics_inv_remove_true':
  assumes "y \<noteq> z"
  shows "matrix_semantics (I(z := True, y := b)) (matrix_assign (P z) matrix)
        = matrix_semantics (I(z := True, y := b)) matrix"
  using assms matrix_semantics_inv_remove_true fun_upd_twist by metis

lemma matrix_semantics_inv_remove_false:
  "matrix_semantics (I(z := False)) (matrix_assign (N z) matrix)
  = matrix_semantics (I(z := False)) matrix"
proof (induction matrix)
  case Nil
  then show ?case by simp
next
  case (Cons cl cls)
  then show ?case
  proof (cases "N z \<in> set cl")
    case True
    hence 0: "clause_semantics (I(z := False)) cl" by (induction cl) auto
    have "matrix_semantics (I(z := False)) (matrix_assign (N z) (cl # cls))
         = matrix_semantics (I(z := False)) (matrix_assign (N z) cls)"
      using 0 clause_semantics_inv_remove_true by simp
    moreover have "matrix_semantics (I(z := False)) (cl # cls)
                  = matrix_semantics (I(z := False)) cls"
      using 0 by simp
    ultimately show ?thesis using Cons by blast
  next
    case False
    hence "matrix_assign (N z) (cl # cls) = remove_lit_neg (N z) cl # matrix_assign (N z) cls"
      by (induction cl) auto
    hence "matrix_semantics (I(z := False)) (matrix_assign (N z) (cl # cls))
          \<longleftrightarrow> clause_semantics (I(z := False)) (remove_lit_neg (N z) cl)
            \<and> matrix_semantics (I(z := False)) (matrix_assign (N z) cls)" by simp
    moreover have "matrix_semantics (I(z := False)) (cl # cls)
                  \<longleftrightarrow> clause_semantics (I(z := False)) cl
                    \<and> matrix_semantics (I(z := False)) cls" by simp
    ultimately show ?thesis using Cons clause_semantics_inv_remove_true by blast
  qed
qed

lemma matrix_semantics_inv_remove_false':
  assumes "y \<noteq> z"
  shows "matrix_semantics (I(z := False, y := b)) (matrix_assign (N z) matrix)
        = matrix_semantics (I(z := False, y := b)) matrix"
  using assms matrix_semantics_inv_remove_false fun_upd_twist by metis

(* The matrix semantics are true for some I iff they are true for some matrix assignment. *)
lemma matrix_semantics_disj_iff_true_assgn:
  "(\<exists>b. matrix_semantics (I(z := b)) matrix)
  \<longleftrightarrow> matrix_semantics (I(z := True)) (matrix_assign (P z) matrix)
    \<or> matrix_semantics (I(z := False)) (matrix_assign (N z) matrix)"
  using matrix_semantics_inv_remove_true matrix_semantics_inv_remove_false by (metis (full_types))

(* The matrix semantics are true for all I iff they are true for both matrix assignments. *)
lemma matrix_semantics_conj_iff_true_assgn:
  "(\<forall>b. matrix_semantics (I(z := b)) matrix)
  \<longleftrightarrow> matrix_semantics (I(z := True)) (matrix_assign (P z) matrix)
    \<and> matrix_semantics (I(z := False)) (matrix_assign (N z) matrix)"
  using matrix_semantics_inv_remove_true matrix_semantics_inv_remove_false by (metis (full_types))

(* A pcnf assignment for a variable not in the prefix is equal to a matrix assignment. *)
lemma pcnf_assign_free_eq_matrix_assgn':
  assumes "lit_var lit \<notin> set (prefix_variables_aux (convert (prefix, matrix)))"
  shows "pcnf_assign lit (prefix, matrix) = (prefix, matrix_assign lit matrix)"
  using assms
  by (induction "(prefix, matrix)" arbitrary: prefix rule: convert.induct) auto

lemma pcnf_assign_free_eq_matrix_assgn:
  assumes "lit_var lit \<notin> set (pcnf_prefix_variables (prefix, matrix))"
  shows "pcnf_assign lit (prefix, matrix) = (prefix, matrix_assign lit matrix)"
  using assms pcnf_assign_free_eq_matrix_assgn' by simp

(* Lemmas for variables not in prefix. *)
lemma neq_first_if_notin_all_prefix:
  "z \<notin> set (pcnf_prefix_variables (UniversalFirst (y, ys) qs, matrix)) \<Longrightarrow> z \<noteq> y"
  by (induction "(UniversalFirst (y, ys) qs, matrix)" rule: convert.induct) auto

lemma neq_first_if_notin_ex_prefix:
  "z \<notin> set (pcnf_prefix_variables (ExistentialFirst (x, xs) qs, matrix)) \<Longrightarrow> z \<noteq> x"
  by (induction "(ExistentialFirst (x, xs) qs, matrix)" rule: convert.induct) auto

lemma notin_pop_prefix_if_notin_prefix:
  assumes "z \<notin> set (pcnf_prefix_variables (prefix, matrix))"
  shows "z \<notin> set (pcnf_prefix_variables (prefix_pop prefix, matrix))"
  using assms
proof (induction prefix)
  case (UniversalFirst q qs)
  then show ?case
  proof (induction q)
    case (Pair y ys)
    then show ?case
      by (induction "(UniversalFirst (y, ys) qs, matrix)" rule: convert.induct) auto
  qed
next
  case (ExistentialFirst q qs)
  then show ?case
  proof (induction q)
    case (Pair x xs)
    then show ?case
      by (induction "(ExistentialFirst (x, xs) qs, matrix)" rule: convert.induct) auto
  qed
next
  case Empty
  then show ?case by simp
qed  

(* The pcnf semantics are invariant when assigning true literals. *)
lemma pcnf_semantics_inv_matrix_assign_true:
  assumes "z \<notin> set (pcnf_prefix_variables (prefix, matrix))"
  shows "pcnf_semantics (I(z := True)) (prefix, matrix_assign (P z) matrix)
        = pcnf_semantics (I(z := True)) (prefix, matrix)"
  using assms
proof (induction I "(prefix, matrix)" arbitrary: I prefix matrix rule: pcnf_semantics.induct)
  case (1 I matrix)
  then show ?case using matrix_semantics_inv_remove_true by simp
next
  case (2 I y matrix)
  then show ?case using matrix_semantics_inv_remove_true' by simp
next
  case (3 I x matrix)
  then show ?case using matrix_semantics_inv_remove_true' by simp
next
  case (4 I y q qs matrix)
  hence neq: "z \<noteq> y" using neq_first_if_notin_all_prefix by blast
  have "prefix_pop (UniversalFirst (y, []) (q # qs)) = ExistentialFirst q qs"
    by (induction q) auto
  hence "z \<notin> set (pcnf_prefix_variables (ExistentialFirst q qs, matrix))"
    using 4(3) notin_pop_prefix_if_notin_prefix by metis
  hence "pcnf_semantics (I(z := True)) (ExistentialFirst q qs, matrix) =
    pcnf_semantics (I(z := True)) (ExistentialFirst q qs, matrix_assign (P z) matrix)"
    for I using 4 by blast
  then show ?case using neq by (simp add: fun_upd_twist)
next
  case (5 I x q qs matrix)
  hence neq: "z \<noteq> x" using neq_first_if_notin_ex_prefix by blast
  have "prefix_pop (ExistentialFirst (x, []) (q # qs)) = UniversalFirst q qs"
    by (induction q) auto
  hence "z \<notin> set (pcnf_prefix_variables (UniversalFirst q qs, matrix))"
    using 5(3) notin_pop_prefix_if_notin_prefix by metis
  hence "pcnf_semantics (I(z := True)) (UniversalFirst q qs, matrix) =
    pcnf_semantics (I(z := True)) (UniversalFirst q qs, matrix_assign (P z) matrix)"
    for I using 5 by blast
  then show ?case using neq by (simp add: fun_upd_twist)
next
  case (6 I y yy ys qs matrix)
  hence neq: "z \<noteq> y" using neq_first_if_notin_all_prefix by blast
  have "z \<notin> set (pcnf_prefix_variables (UniversalFirst (yy, ys) qs, matrix))"
    using 6(3) notin_pop_prefix_if_notin_prefix by fastforce
  hence "pcnf_semantics (I(z := True)) (UniversalFirst (yy, ys) qs, matrix) =
    pcnf_semantics (I(z := True)) (UniversalFirst (yy, ys) qs, matrix_assign (P z) matrix)"
    for I using 6 by blast
  then show ?case using neq by (simp add: fun_upd_twist)
next
  case (7 I x xx xs qs matrix)
  hence neq: "z \<noteq> x" using neq_first_if_notin_ex_prefix by blast
  have "z \<notin> set (pcnf_prefix_variables (ExistentialFirst (xx, xs) qs, matrix))"
    using 7(3) notin_pop_prefix_if_notin_prefix by fastforce
  hence "pcnf_semantics (I(z := True)) (ExistentialFirst (xx, xs) qs, matrix) =
    pcnf_semantics (I(z := True)) (ExistentialFirst (xx, xs) qs, matrix_assign (P z) matrix)"
    for I using 7 by blast
  then show ?case using neq by (simp add: fun_upd_twist)
qed

lemma pcnf_semantics_inv_matrix_assign_false:
  assumes "z \<notin> set (pcnf_prefix_variables (prefix, matrix))"
  shows "pcnf_semantics (I(z := False)) (prefix, matrix_assign (N z) matrix)
        = pcnf_semantics (I(z := False)) (prefix, matrix)"
  using assms
proof (induction I "(prefix, matrix)" arbitrary: I prefix matrix rule: pcnf_semantics.induct)
  case (1 I matrix)
  then show ?case using matrix_semantics_inv_remove_false by simp
next
  case (2 I y matrix)
  then show ?case using matrix_semantics_inv_remove_false' by simp
next
  case (3 I x matrix)
  then show ?case using matrix_semantics_inv_remove_false' by simp
next
  case (4 I y q qs matrix)
  hence neq: "z \<noteq> y" using neq_first_if_notin_all_prefix by blast
  have "prefix_pop (UniversalFirst (y, []) (q # qs)) = ExistentialFirst q qs"
    by (induction q) auto
  hence "z \<notin> set (pcnf_prefix_variables (ExistentialFirst q qs, matrix))"
    using 4(3) notin_pop_prefix_if_notin_prefix by metis
  hence "pcnf_semantics (I(z := False)) (ExistentialFirst q qs, matrix) =
    pcnf_semantics (I(z := False)) (ExistentialFirst q qs, matrix_assign (N z) matrix)"
    for I using 4 by blast
  then show ?case using neq by (simp add: fun_upd_twist)
next
  case (5 I x q qs matrix)
  hence neq: "z \<noteq> x" using neq_first_if_notin_ex_prefix by blast
  have "prefix_pop (ExistentialFirst (x, []) (q # qs)) = UniversalFirst q qs"
    by (induction q) auto
  hence "z \<notin> set (pcnf_prefix_variables (UniversalFirst q qs, matrix))"
    using 5(3) notin_pop_prefix_if_notin_prefix by metis
  hence "pcnf_semantics (I(z := False)) (UniversalFirst q qs, matrix) =
    pcnf_semantics (I(z := False)) (UniversalFirst q qs, matrix_assign (N z) matrix)"
    for I using 5 by blast
  then show ?case using neq by (simp add: fun_upd_twist)
next
  case (6 I y yy ys qs matrix)
  hence neq: "z \<noteq> y" using neq_first_if_notin_all_prefix by blast
  have "z \<notin> set (pcnf_prefix_variables (UniversalFirst (yy, ys) qs, matrix))"
    using 6(3) notin_pop_prefix_if_notin_prefix by fastforce
  hence "pcnf_semantics (I(z := False)) (UniversalFirst (yy, ys) qs, matrix) =
    pcnf_semantics (I(z := False)) (UniversalFirst (yy, ys) qs, matrix_assign (N z) matrix)"
    for I using 6 by blast
  then show ?case using neq by (simp add: fun_upd_twist)
next
  case (7 I x xx xs qs matrix)
  hence neq: "z \<noteq> x" using neq_first_if_notin_ex_prefix by blast
  have "z \<notin> set (pcnf_prefix_variables (ExistentialFirst (xx, xs) qs, matrix))"
    using 7(3) notin_pop_prefix_if_notin_prefix by fastforce
  hence "pcnf_semantics (I(z := False)) (ExistentialFirst (xx, xs) qs, matrix) =
    pcnf_semantics (I(z := False)) (ExistentialFirst (xx, xs) qs, matrix_assign (N z) matrix)"
    for I using 7 by blast
  then show ?case using neq by (simp add: fun_upd_twist)
qed

(* Disjunctions of the pcnf semantics are invariant when assigning true literals. *)
lemma pcnf_semantics_disj_iff_matrix_assign_disj:
  assumes "z \<notin> set (pcnf_prefix_variables (prefix, matrix))"
  shows "pcnf_semantics (I(z := True)) (prefix, matrix)
        \<or> pcnf_semantics (I(z := False)) (prefix, matrix)
        \<longleftrightarrow>
        pcnf_semantics (I(z := True)) (prefix, matrix_assign (P z) matrix)
        \<or> pcnf_semantics (I(z := False)) (prefix, matrix_assign (N z) matrix)"
  using assms
proof (induction I "(prefix, matrix_assign (P z) matrix)"
    arbitrary: I prefix matrix rule: pcnf_semantics.induct)
  case (1 I)
  then show ?case using ex_bool_eq matrix_semantics_disj_iff_true_assgn by simp
next
  case (2 I y)
  hence neq: "y \<noteq> z" by simp
  show ?case using ex_bool_eq matrix_semantics_inv_remove_true'
      matrix_semantics_inv_remove_false' neq by simp
next
  case (3 I x)
  hence neq: "x \<noteq> z" by simp
  show ?case using ex_bool_eq matrix_semantics_inv_remove_true'
      matrix_semantics_inv_remove_false' neq by simp
next
  case (4 I y q qs)
  hence neq: "y \<noteq> z" using neq_first_if_notin_all_prefix by blast
  have "prefix_pop (UniversalFirst (y, []) (q # qs)) = ExistentialFirst q qs"
    by (induction q) auto
  hence nin: "z \<notin> set (pcnf_prefix_variables (ExistentialFirst q qs, matrix))"
    using 4(3) notin_pop_prefix_if_notin_prefix by metis
  show ?case using nin neq pcnf_semantics_inv_matrix_assign_true
      pcnf_semantics_inv_matrix_assign_false by (simp add: fun_upd_twist)
next
  case (5 I x q qs)
  hence neq: "x \<noteq> z" using neq_first_if_notin_ex_prefix by blast
  have "prefix_pop (ExistentialFirst (x, []) (q # qs)) = UniversalFirst q qs"
    by (induction q) auto
  hence nin: "z \<notin> set (pcnf_prefix_variables (UniversalFirst q qs, matrix))"
    using 5(3) notin_pop_prefix_if_notin_prefix by metis
  show ?case using nin neq pcnf_semantics_inv_matrix_assign_true
      pcnf_semantics_inv_matrix_assign_false by (simp add: fun_upd_twist)
next
  case (6 I y yy ys qs)
  hence neq: "y \<noteq> z" using neq_first_if_notin_all_prefix by blast
  have nin: "z \<notin> set (pcnf_prefix_variables (UniversalFirst (yy, ys) qs, matrix))"
    using 6(3) notin_pop_prefix_if_notin_prefix by fastforce
  show ?case using nin neq pcnf_semantics_inv_matrix_assign_true
      pcnf_semantics_inv_matrix_assign_false by (simp add: fun_upd_twist)
next
  case (7 I x xx xs qs)
  hence neq: "x \<noteq> z" using neq_first_if_notin_ex_prefix by blast
  have nin: "z \<notin> set (pcnf_prefix_variables (ExistentialFirst (xx, xs) qs, matrix))"
    using 7(3) notin_pop_prefix_if_notin_prefix by fastforce
  show ?case using nin neq pcnf_semantics_inv_matrix_assign_true
      pcnf_semantics_inv_matrix_assign_false by (simp add: fun_upd_twist)
qed

(* Conjunctions of the pcnf semantics are invariant when assigning true literals. *)
lemma pcnf_semantics_conj_iff_matrix_assign_conj:
  assumes "z \<notin> set (pcnf_prefix_variables (prefix, matrix))"
  shows "pcnf_semantics (I(z := True)) (prefix, matrix)
        \<and> pcnf_semantics (I(z := False)) (prefix, matrix)
        \<longleftrightarrow>
        pcnf_semantics (I(z := True)) (prefix, matrix_assign (P z) matrix)
        \<and> pcnf_semantics (I(z := False)) (prefix, matrix_assign (N z) matrix)"
  using assms
proof (induction I "(prefix, matrix_assign (P z) matrix)"
    arbitrary: I prefix matrix rule: pcnf_semantics.induct)
  case (1 I)
  then show ?case using all_bool_eq matrix_semantics_conj_iff_true_assgn by simp
next
  case (2 I y)
  hence neq: "y \<noteq> z" by simp
  show ?case using matrix_semantics_inv_remove_true'
      matrix_semantics_inv_remove_false' neq by simp
next
  case (3 I x)
  hence neq: "x \<noteq> z" by simp
  show ?case using matrix_semantics_inv_remove_true'
      matrix_semantics_inv_remove_false' neq by simp
next
  case (4 I y q qs)
  hence neq: "y \<noteq> z" using neq_first_if_notin_all_prefix by blast
  have "prefix_pop (UniversalFirst (y, []) (q # qs)) = ExistentialFirst q qs"
    by (induction q) auto
  hence nin: "z \<notin> set (pcnf_prefix_variables (ExistentialFirst q qs, matrix))"
    using 4(3) notin_pop_prefix_if_notin_prefix by metis
  show ?case using nin neq pcnf_semantics_inv_matrix_assign_true
      pcnf_semantics_inv_matrix_assign_false by (simp add: fun_upd_twist)
next
  case (5 I x q qs)
  hence neq: "x \<noteq> z" using neq_first_if_notin_ex_prefix by blast
  have "prefix_pop (ExistentialFirst (x, []) (q # qs)) = UniversalFirst q qs"
    by (induction q) auto
  hence nin: "z \<notin> set (pcnf_prefix_variables (UniversalFirst q qs, matrix))"
    using 5(3) notin_pop_prefix_if_notin_prefix by metis
  show ?case using nin neq pcnf_semantics_inv_matrix_assign_true
      pcnf_semantics_inv_matrix_assign_false by (simp add: fun_upd_twist)
next
  case (6 I y yy ys qs)
  hence neq: "y \<noteq> z" using neq_first_if_notin_all_prefix by blast
  have nin: "z \<notin> set (pcnf_prefix_variables (UniversalFirst (yy, ys) qs, matrix))"
    using 6(3) notin_pop_prefix_if_notin_prefix by fastforce
  show ?case using nin neq pcnf_semantics_inv_matrix_assign_true
      pcnf_semantics_inv_matrix_assign_false by (simp add: fun_upd_twist)
next
  case (7 I x xx xs qs)
  hence neq: "x \<noteq> z" using neq_first_if_notin_ex_prefix by blast
  have nin: "z \<notin> set (pcnf_prefix_variables (ExistentialFirst (xx, xs) qs, matrix))"
    using 7(3) notin_pop_prefix_if_notin_prefix by fastforce
  show ?case using nin neq pcnf_semantics_inv_matrix_assign_true
      pcnf_semantics_inv_matrix_assign_false by (simp add: fun_upd_twist)
qed

(* Semantics are equal under two interpretations if they agree on the free variables. *)
lemma semantics_eq_if_free_vars_eq:
  assumes "\<forall>x \<in> set (free_variables qbf). I(x) = J(x)"
  shows "qbf_semantics I qbf = qbf_semantics J qbf" using assms
proof (induction I qbf rule: qbf_semantics.induct)
  case (1 I z)
  then show ?case by simp
next
  case (2 I qbf)
  then show ?case by simp
next
  case (3 I qbf_list)
  then show ?case by (induction qbf_list) auto
next
  case (4 I qbf_list)
  then show ?case by (induction qbf_list) auto
next
  case (5 I x qbf)
  hence "qbf_semantics I (substitute_var x b qbf)
        = qbf_semantics J (substitute_var x b qbf)"
    for b using set_free_vars_subst_ex_eq by (metis (full_types))
  then show ?case by simp
next
  case (6 I x qbf)
  hence "qbf_semantics I (substitute_var x b qbf)
        = qbf_semantics J (substitute_var x b qbf)"
    for b using set_free_vars_subst_all_eq by (metis (full_types))
  then show ?case by simp
qed

lemma pcnf_semantics_eq_if_free_vars_eq:
  assumes "\<forall>x \<in> set (pcnf_free_variables pcnf). I(x) = J(x)"
  shows "pcnf_semantics I pcnf = pcnf_semantics J pcnf"
  using assms semantics_eq_if_free_vars_eq qbf_semantics_eq_pcnf_semantics by simp

(* Interpretation value of assigned variables does not matter *)
lemma x_notin_assign_P_x:
  "x \<notin> set (pcnf_variables (pcnf_assign (P x) pcnf))"
  using pcnf_assign_vars_subseteq_vars_minus_lit by fastforce

lemma x_notin_assign_N_x:
  "x \<notin> set (pcnf_variables (pcnf_assign (N x) pcnf))"
  using pcnf_assign_vars_subseteq_vars_minus_lit by fastforce

lemma interp_value_ignored_for_pcnf_P_assign:
  "pcnf_semantics (I(x := b)) (pcnf_assign (P x) pcnf)
  = pcnf_semantics I (pcnf_assign (P x) pcnf)"
  using pcnf_semantics_eq_if_free_vars_eq x_notin_assign_P_x
    pcnf_free_eq_vars_minus_prefix by simp

lemma interp_value_ignored_for_pcnf_N_assign:
  "pcnf_semantics (I(x := b)) (pcnf_assign (N x) pcnf)
  = pcnf_semantics I (pcnf_assign (N x) pcnf)"
  using pcnf_semantics_eq_if_free_vars_eq x_notin_assign_N_x
    pcnf_free_eq_vars_minus_prefix by simp

(* A pcnf starting with an existential is satisfiable iff both possible assignments are. *)
lemma sat_ex_first_iff_one_assign_sat:
  assumes "x \<notin> set (pcnf_prefix_variables (prefix_pop (ExistentialFirst (x, xs) qs), matrix))"
  shows "satisfiable (convert (ExistentialFirst (x, xs) qs, matrix))
  \<longleftrightarrow> satisfiable (convert (pcnf_assign (P x) (ExistentialFirst (x, xs) qs, matrix)))
    \<or> satisfiable (convert (pcnf_assign (N x) (ExistentialFirst (x, xs) qs, matrix)))"
proof -
  let ?pre = "ExistentialFirst (x, xs) qs"
  have "satisfiable (convert (?pre, matrix))
       = (\<exists>I. pcnf_semantics I (?pre, matrix))"
    using satisfiable_def qbf_semantics_eq_pcnf_semantics by simp
  also have "... =
       (\<exists>I. pcnf_semantics (I(x := True)) (prefix_pop ?pre, matrix) \<or>
            pcnf_semantics (I(x := False)) (prefix_pop ?pre, matrix))"
    by (induction "?pre" rule: prefix_pop.induct) auto
  also have "... =
    (\<exists>I. pcnf_semantics (I(x := True)) (prefix_pop ?pre, matrix_assign (P x) matrix) \<or>
         pcnf_semantics (I(x := False)) (prefix_pop ?pre, matrix_assign (N x) matrix))"
    using pcnf_semantics_disj_iff_matrix_assign_disj assms by blast
  also have "... \<longleftrightarrow>
    (\<exists>I. pcnf_semantics (I(x := True)) (pcnf_assign (P x) (?pre, matrix))) \<or>
    (\<exists>I. pcnf_semantics (I(x := False)) (pcnf_assign (N x) (?pre, matrix)))"
    using pcnf_assign_free_eq_matrix_assgn[of "P x"] pcnf_assign_free_eq_matrix_assgn[of "N x"]
      assms by auto
  also have "... \<longleftrightarrow>
    (\<exists>I. pcnf_semantics I (pcnf_assign (P x) (?pre, matrix))) \<or>
    (\<exists>I. pcnf_semantics I (pcnf_assign (N x) (?pre, matrix)))"
    using interp_value_ignored_for_pcnf_N_assign interp_value_ignored_for_pcnf_P_assign
    by blast
  also have "... \<longleftrightarrow>
    satisfiable (convert (pcnf_assign (P x) (?pre, matrix))) \<or>
    satisfiable (convert (pcnf_assign (N x) (?pre, matrix)))"
    using satisfiable_def qbf_semantics_eq_pcnf_semantics by simp
  finally show ?thesis .
qed

(* A pcnf starting with an existential is satisfiable
  iff the disjunction of both possible assignments is.
  That is: \<exists>x\<Phi> \<approx>sat \<Phi>_x \<or> \<Phi>_\<not>x. *)
theorem sat_ex_first_iff_assign_disj_sat:
  assumes "x \<notin> set (pcnf_prefix_variables (prefix_pop (ExistentialFirst (x, xs) qs), matrix))"
  shows "satisfiable (convert (ExistentialFirst (x, xs) qs, matrix))
  \<longleftrightarrow> satisfiable (Disj
    [convert (pcnf_assign (P x) (ExistentialFirst (x, xs) qs, matrix)),
     convert (pcnf_assign (N x) (ExistentialFirst (x, xs) qs, matrix))])"
  using assms sat_ex_first_iff_one_assign_sat satisfiable_def
    qbf_semantics_eq_pcnf_semantics by auto

(* A pcnf starting with an universal is satisfiable
  iff the disjunction of both possible assignments is. 
  That is: \<forall>y\<Phi> \<approx>sat \<Phi>_y \<and> \<Phi>_\<not>y. *)
theorem sat_all_first_iff_assign_conj_sat:
  assumes "y \<notin> set (pcnf_prefix_variables (prefix_pop (UniversalFirst (y, ys) qs), matrix))"
  shows "satisfiable (convert (UniversalFirst (y, ys) qs, matrix))
  \<longleftrightarrow> satisfiable (Conj
    [convert (pcnf_assign (P y) (UniversalFirst (y, ys) qs, matrix)),
     convert (pcnf_assign (N y) (UniversalFirst (y, ys) qs, matrix))])"
proof -
  let ?pre = "UniversalFirst (y, ys) qs"
  have "satisfiable (convert (?pre, matrix))
       = (\<exists>I. pcnf_semantics I (?pre, matrix))"
    using satisfiable_def qbf_semantics_eq_pcnf_semantics by simp
  also have "... =
    (\<exists>I. pcnf_semantics (I(y := True)) (prefix_pop ?pre, matrix) \<and>
         pcnf_semantics (I(y := False)) (prefix_pop ?pre, matrix))"
    by (induction "?pre" rule: prefix_pop.induct) auto
  also have "... =
    (\<exists>I. pcnf_semantics (I(y := True)) (prefix_pop ?pre, matrix_assign (P y) matrix) \<and>
         pcnf_semantics (I(y := False)) (prefix_pop ?pre, matrix_assign (N y) matrix))"
    using pcnf_semantics_conj_iff_matrix_assign_conj assms by blast
  also have "... =
    (\<exists>I. pcnf_semantics (I(y := True)) (pcnf_assign (P y) (?pre, matrix)) \<and>
         pcnf_semantics (I(y := False)) (pcnf_assign (N y) (?pre, matrix)))"
    using pcnf_assign_free_eq_matrix_assgn[of "P y"] pcnf_assign_free_eq_matrix_assgn[of "N y"]
      assms by simp
  also have "... =
    (\<exists>I. pcnf_semantics I (pcnf_assign (P y) (?pre, matrix)) \<and>
         pcnf_semantics I (pcnf_assign (N y) (?pre, matrix)))"
    using interp_value_ignored_for_pcnf_N_assign interp_value_ignored_for_pcnf_P_assign by blast
  also have "... =
    (\<exists>I. qbf_semantics I (convert (pcnf_assign (P y) (?pre, matrix))) \<and>
         qbf_semantics I (convert (pcnf_assign (N y) (?pre, matrix))))"
      using qbf_semantics_eq_pcnf_semantics by blast
  also have "... =
    satisfiable (Conj
      [convert (pcnf_assign (P y) (?pre, matrix)),
       convert (pcnf_assign (N y) (?pre, matrix))])"
    unfolding satisfiable_def by simp
  finally show ?thesis .
qed

(***
End of proof showing:
\<exists>x\<Phi> \<approx>sat \<Phi>_x \<or> \<Phi>_\<not>x and \<forall>y\<Phi> \<approx>sat \<Phi>_y \<and> \<Phi>_\<not>y
if x/y is the first variable in the prefix.
***)

(* definition of cleansed formula and properties of cleansed formulas *)
fun cleansed_p :: "pcnf \<Rightarrow> bool" where
"cleansed_p pcnf = distinct (prefix_variables_aux (convert pcnf))"

lemma prefix_pop_cleansed_if_cleansed:
  "cleansed_p (prefix, matrix) \<Longrightarrow> cleansed_p (prefix_pop prefix, matrix)"
  by (induction prefix rule: prefix_pop.induct) auto

lemma prefix_variables_aux_matrix_inv:
  "prefix_variables_aux (convert (prefix, matrix1))
  = prefix_variables_aux (convert (prefix, matrix2))"
  by (induction "(prefix, matrix1)" arbitrary: prefix rule: convert.induct) auto

lemma eq_prefix_cleansed_p_add_all_inv:
  "cleansed_p (add_universal_to_front y (prefix, matrix1))
  = cleansed_p (add_universal_to_front y (prefix, matrix2))"
proof (induction y "(prefix, matrix1)" arbitrary: prefix rule: add_universal_to_front.induct)
  case (1 x)
  then show ?case by simp
next
  case (2 x y ys qs)
  have "prefix_variables_aux (convert (UniversalFirst (y, ys) qs, matrix1))
       = prefix_variables_aux (convert (UniversalFirst (y, ys) qs, matrix2))"
    using prefix_variables_aux_matrix_inv by simp
  then show ?case by simp
next
  case (3 x y ys qs)
    have "prefix_variables_aux (convert (ExistentialFirst (y, ys) qs, matrix1))
       = prefix_variables_aux (convert (ExistentialFirst (y, ys) qs, matrix2))"
    using prefix_variables_aux_matrix_inv by simp
  then show ?case by simp
qed

lemma eq_prefix_cleansed_p_add_ex_inv:
  "cleansed_p (add_existential_to_front x (prefix, matrix1))
  = cleansed_p (add_existential_to_front x (prefix, matrix2))"
proof (induction x "(prefix, matrix1)" arbitrary: prefix rule: add_universal_to_front.induct)
  case (1 x)
  then show ?case by simp
next
  case (2 x y ys qs)
  have "prefix_variables_aux (convert (UniversalFirst (y, ys) qs, matrix1))
       = prefix_variables_aux (convert (UniversalFirst (y, ys) qs, matrix2))"
    using prefix_variables_aux_matrix_inv by simp
  then show ?case by simp
next
  case (3 x y ys qs)
    have "prefix_variables_aux (convert (ExistentialFirst (y, ys) qs, matrix1))
       = prefix_variables_aux (convert (ExistentialFirst (y, ys) qs, matrix2))"
    using prefix_variables_aux_matrix_inv by simp
  then show ?case by simp
qed

lemma cleansed_p_matrix_inv:
  "cleansed_p (prefix, matrix1) = cleansed_p (prefix, matrix2)"
proof (induction "(prefix, matrix1)" arbitrary: prefix rule: convert.induct)
  case 1
  then show ?case by simp
next
  case (2 x)
  then show ?case by simp
next
  case (3 x)
  then show ?case by simp
next
  case (4 x q qs)
  have "(UniversalFirst (x, []) (q # qs), matrix)
       = add_universal_to_front x (ExistentialFirst q qs, matrix)"
    for matrix by (induction q) auto
  then show ?case using eq_prefix_cleansed_p_add_all_inv by simp 
next
  case (5 x q qs)
    have "(ExistentialFirst (x, []) (q # qs), matrix)
       = add_existential_to_front x (UniversalFirst q qs, matrix)"
    for matrix by (induction q) auto
  then show ?case using eq_prefix_cleansed_p_add_ex_inv by simp
next
  case (6 x y ys qs)
  have "(UniversalFirst (x, y # ys) qs, matrix)
       = add_universal_to_front x (UniversalFirst (y, ys) qs, matrix)"
    for matrix by simp
  then show ?case using eq_prefix_cleansed_p_add_all_inv by metis
next
  case (7 x y ys qs)
  have "(ExistentialFirst (x, y # ys) qs, matrix)
       = add_existential_to_front x (ExistentialFirst (y, ys) qs, matrix)"
    for matrix by simp
  then show ?case using eq_prefix_cleansed_p_add_ex_inv by metis
qed

lemma cleansed_prefix_first_ex_unique:
  assumes "cleansed_p (ExistentialFirst (x, xs) qs, matrix)"
  shows "x \<notin> set (pcnf_prefix_variables (prefix_pop (ExistentialFirst (x, xs) qs), matrix))"
  using assms by (induction "ExistentialFirst (x, xs) qs" rule: prefix_pop.induct) auto

lemma cleansed_prefix_first_all_unique:
  assumes "cleansed_p (UniversalFirst (y, ys) qs, matrix)"
  shows "y \<notin> set (pcnf_prefix_variables (prefix_pop (UniversalFirst (y, ys) qs), matrix))"
  using assms by (induction "UniversalFirst (y, ys) qs" rule: prefix_pop.induct) auto

lemma cleansed_add_new_ex_to_front:
  assumes "cleansed_p pcnf"
    and "x \<notin> set (pcnf_prefix_variables pcnf)"
  shows "cleansed_p (add_existential_to_front x pcnf)"
  using assms by (induction x pcnf rule: add_existential_to_front.induct) auto

lemma cleansed_add_new_all_to_front:
  assumes "cleansed_p pcnf"
    and "y \<notin> set (pcnf_prefix_variables pcnf)"
  shows "cleansed_p (add_universal_to_front y pcnf)"
  using assms by (induction y pcnf rule: add_existential_to_front.induct) auto

lemma pcnf_assign_p_ex_eq:
  assumes "cleansed_p (ExistentialFirst (x, xs) qs, matrix)"
  shows "pcnf_assign (P x) (ExistentialFirst (x, xs) qs, matrix)
        = (prefix_pop (ExistentialFirst (x, xs) qs), matrix_assign (P x) matrix)"
  using assms by (metis cleansed_prefix_first_ex_unique lit_var.simps(1)
      pcnf_assign.simps pcnf_assign_free_eq_matrix_assgn remove_var_prefix.simps(3))

lemma pcnf_assign_p_all_eq:
  assumes "cleansed_p (UniversalFirst (y, ys) qs, matrix)"
  shows "pcnf_assign (P y) (UniversalFirst (y, ys) qs, matrix)
        = (prefix_pop (UniversalFirst (y, ys) qs), matrix_assign (P y) matrix)"
  using assms by (metis cleansed_prefix_first_all_unique lit_var.simps(1)
      pcnf_assign.simps pcnf_assign_free_eq_matrix_assgn remove_var_prefix.simps(2))

lemma pcnf_assign_n_ex_eq:
  assumes "cleansed_p (ExistentialFirst (x, xs) qs, matrix)"
  shows "pcnf_assign (N x) (ExistentialFirst (x, xs) qs, matrix)
        = (prefix_pop (ExistentialFirst (x, xs) qs), matrix_assign (N x) matrix)"
  using assms by (metis cleansed_prefix_first_ex_unique lit_var.simps(2)
      pcnf_assign.simps pcnf_assign_free_eq_matrix_assgn remove_var_prefix.simps(3))

lemma pcnf_assign_n_all_eq:
  assumes "cleansed_p (UniversalFirst (y, ys) qs, matrix)"
  shows "pcnf_assign (N y) (UniversalFirst (y, ys) qs, matrix)
        = (prefix_pop (UniversalFirst (y, ys) qs), matrix_assign (N y) matrix)"
  using assms by (metis cleansed_prefix_first_all_unique lit_var.simps(2)
      pcnf_assign.simps pcnf_assign_free_eq_matrix_assgn remove_var_prefix.simps(2))

(* pcnf cleansing formalization *)
function pcnf_cleanse :: "pcnf \<Rightarrow> pcnf" where
"pcnf_cleanse (Empty, matrix) = (Empty, matrix)" |
"pcnf_cleanse (UniversalFirst (y, ys) qs, matrix) =
  (if y \<in> set (pcnf_prefix_variables (prefix_pop (UniversalFirst (y, ys) qs), matrix))
    then pcnf_cleanse (prefix_pop (UniversalFirst (y, ys) qs), matrix)
    else add_universal_to_front y
      (pcnf_cleanse (prefix_pop (UniversalFirst (y, ys) qs), matrix)))" |
"pcnf_cleanse (ExistentialFirst (x, xs) qs, matrix) =
  (if x \<in> set (pcnf_prefix_variables (prefix_pop (ExistentialFirst (x, xs) qs), matrix))
    then pcnf_cleanse (prefix_pop (ExistentialFirst (x, xs) qs), matrix)
    else add_existential_to_front x
      (pcnf_cleanse (prefix_pop (ExistentialFirst (x, xs) qs), matrix)))"
  by pat_completeness auto
termination
  by (relation "measure (\<lambda>(pre, mat). prefix_measure pre)")
     (auto simp add: prefix_pop_decreases_measure simp del: prefix_measure.simps)

value "pcnf_cleanse (UniversalFirst (0, [0]) [(0, [1, 2, 0, 1])], [])"

(* cleansing preserves free variables *)
lemma prefix_pop_all_prefix_vars_set:
  "set (pcnf_prefix_variables (UniversalFirst (y, ys) qs, matrix))
  = {y} \<union> set (pcnf_prefix_variables (prefix_pop (UniversalFirst (y, ys) qs), matrix))"
  by (induction "(UniversalFirst (y, ys) qs, matrix)" rule: convert.induct, induction qs) auto

lemma prefix_pop_ex_prefix_vars_set:
  "set (pcnf_prefix_variables (ExistentialFirst (x, xs) qs, matrix))
  = {x} \<union> set (pcnf_prefix_variables (prefix_pop (ExistentialFirst (x, xs) qs), matrix))"
  by (induction "(ExistentialFirst (x, xs) qs, matrix)" rule: convert.induct, induction qs) auto

lemma cleanse_prefix_vars_inv:
  "set (pcnf_prefix_variables (prefix, matrix))
  = set (pcnf_prefix_variables (pcnf_cleanse (prefix, matrix)))"
  using add_all_adds_prefix_var prefix_pop_all_prefix_vars_set
    add_ex_adds_prefix_var prefix_pop_ex_prefix_vars_set
  by (induction "(prefix, matrix)" arbitrary: prefix rule: pcnf_cleanse.induct) auto

lemma prefix_pop_all_vars_inv:
  "set (pcnf_variables (UniversalFirst (y, ys) qs, matrix))
  = set (pcnf_variables (prefix_pop (UniversalFirst (y, ys) qs), matrix))"
  by (induction "(UniversalFirst (y, ys) qs, matrix)" rule: convert.induct, induction qs) auto

lemma prefix_pop_ex_vars_inv:
  "set (pcnf_variables (ExistentialFirst (x, xs) qs, matrix))
  = set (pcnf_variables (prefix_pop (ExistentialFirst (x, xs) qs), matrix))"
  by (induction "(ExistentialFirst (x, xs) qs, matrix)" rule: convert.induct, induction qs) auto

lemma add_all_vars_inv:
  "set (pcnf_variables (add_universal_to_front y pcnf))
  = set (pcnf_variables pcnf)"
  using convert_add_all by auto

lemma add_ex_vars_inv:
  "set (pcnf_variables (add_existential_to_front x pcnf))
  = set (pcnf_variables pcnf)"
  using convert_add_ex by auto

lemma cleanse_vars_inv:
  "set (pcnf_variables (prefix, matrix))
  = set (pcnf_variables (pcnf_cleanse (prefix, matrix)))"
  using add_all_vars_inv prefix_pop_all_vars_inv
    add_ex_vars_inv prefix_pop_ex_vars_inv
  by (induction "(prefix, matrix)" arbitrary: prefix rule: pcnf_cleanse.induct) auto

theorem cleanse_free_vars_inv:
  "set (pcnf_free_variables pcnf)
  = set (pcnf_free_variables (pcnf_cleanse pcnf))"
  using cleanse_prefix_vars_inv cleanse_vars_inv pcnf_free_eq_vars_minus_prefix
  by (induction pcnf) simp_all

(* cleansed_p holds after cleansing *)
theorem pcnf_cleanse_cleanses:
  "cleansed_p (pcnf_cleanse pcnf)"
  using cleanse_prefix_vars_inv cleansed_add_new_all_to_front cleansed_add_new_ex_to_front
  by (induction pcnf rule: pcnf_cleanse.induct) auto

(* cleansed_p is invariant under pcnf_assign *)
theorem pcnf_assign_cleansed_inv:
  "cleansed_p pcnf \<Longrightarrow> cleansed_p (pcnf_assign lit pcnf)"
proof (induction pcnf rule: convert.induct)
  case (1 matrix)
  then show ?case by simp
next
  case (2 x matrix)
  then show ?case by simp
next
  case (3 x matrix)
  then show ?case by simp
next
  case (4 x q qs matrix)
  let ?z = "lit_var lit"
  show ?case
  proof (cases "x = ?z")
    case True
    then show ?thesis using 4 cleansed_p_matrix_inv
        pcnf_assign_n_all_eq[of ?z] pcnf_assign_p_all_eq[of ?z]
        prefix_pop_cleansed_if_cleansed lit_var.elims by metis
  next
    case False
    let ?mat = "matrix_assign lit matrix"
    have "cleansed_p (remove_var_prefix ?z (ExistentialFirst q qs), ?mat)"
      using 4 by simp
    moreover have "x \<notin> set (pcnf_prefix_variables (remove_var_prefix ?z (ExistentialFirst q qs), ?mat))"
      using 4 False prefix_assign_vars_eq_prefix_vars_minus_lit[of ?z] prefix_vars_matrix_inv
      by fastforce
    ultimately have "cleansed_p (add_universal_to_prefix x (remove_var_prefix ?z (ExistentialFirst q qs)), ?mat)"
      using cleansed_add_new_all_to_front add_all_to_prefix_eq_add_to_front by simp
    then have "cleansed_p (remove_var_prefix ?z (UniversalFirst (x, []) (q # qs)), ?mat)"
      using False by (induction q) auto
    then show ?thesis by simp
  qed
next
  case (5 x q qs matrix)
  let ?z = "lit_var lit"
  show ?case
  proof (cases "x = ?z")
    case True
    then show ?thesis using 5 cleansed_p_matrix_inv
        pcnf_assign_n_ex_eq[of ?z] pcnf_assign_p_ex_eq[of ?z]
        prefix_pop_cleansed_if_cleansed lit_var.elims by metis
  next
    case False
    let ?mat = "matrix_assign lit matrix"
    have "cleansed_p (remove_var_prefix ?z (UniversalFirst q qs), ?mat)"
      using 5 by simp
    moreover have "x \<notin> set (pcnf_prefix_variables (remove_var_prefix ?z (UniversalFirst q qs), ?mat))"
      using 5 False prefix_assign_vars_eq_prefix_vars_minus_lit[of ?z] prefix_vars_matrix_inv
      by fastforce
    ultimately have "cleansed_p (add_existential_to_prefix x (remove_var_prefix ?z (UniversalFirst q qs)), ?mat)"
      using cleansed_add_new_ex_to_front add_ex_to_prefix_eq_add_to_front by simp
    then have "cleansed_p (remove_var_prefix ?z (ExistentialFirst (x, []) (q # qs)), ?mat)"
      using False by (induction q) auto
    then show ?thesis by simp
  qed
next
  case (6 x y ys qs matrix)
  let ?z = "lit_var lit"
  show ?case
  proof (cases "x = ?z")
    case True
    then show ?thesis using 6 cleansed_p_matrix_inv
        pcnf_assign_n_all_eq[of ?z] pcnf_assign_p_all_eq[of ?z]
        prefix_pop_cleansed_if_cleansed lit_var.elims by metis
  next
    case False
    let ?mat = "matrix_assign lit matrix"
    have "cleansed_p (remove_var_prefix ?z (UniversalFirst (y, ys) qs), ?mat)"
      using 6 by simp
    moreover have "x \<notin> set (pcnf_prefix_variables (remove_var_prefix ?z (UniversalFirst (y, ys) qs), ?mat))"
      using 6(2) False prefix_assign_vars_eq_prefix_vars_minus_lit[of ?z] prefix_vars_matrix_inv
      by fastforce
    ultimately have "cleansed_p (add_universal_to_prefix x (remove_var_prefix ?z (UniversalFirst (y, ys) qs)), ?mat)"
      using cleansed_add_new_all_to_front add_all_to_prefix_eq_add_to_front by simp
    then have "cleansed_p (remove_var_prefix ?z (UniversalFirst (x, (y # ys)) qs), ?mat)"
      using False by simp
    then show ?thesis by simp
  qed
next
  case (7 x y ys qs matrix)
  let ?z = "lit_var lit"
  show ?case
  proof (cases "x = ?z")
    case True
    then show ?thesis using 7 cleansed_p_matrix_inv
        pcnf_assign_n_ex_eq[of ?z] pcnf_assign_p_ex_eq[of ?z]
        prefix_pop_cleansed_if_cleansed lit_var.elims by metis
  next
    case False
    let ?mat = "matrix_assign lit matrix"
    have "cleansed_p (remove_var_prefix ?z (ExistentialFirst (y, ys) qs), ?mat)"
      using 7 by simp
    moreover have "x \<notin> set (pcnf_prefix_variables (remove_var_prefix ?z (ExistentialFirst (y, ys) qs), ?mat))"
      using 7(2) False prefix_assign_vars_eq_prefix_vars_minus_lit[of ?z] prefix_vars_matrix_inv
      by fastforce
    ultimately have "cleansed_p (add_existential_to_prefix x (remove_var_prefix ?z (ExistentialFirst (y, ys) qs)), ?mat)"
      using cleansed_add_new_ex_to_front add_ex_to_prefix_eq_add_to_front by simp
    then have "cleansed_p (remove_var_prefix ?z (ExistentialFirst (x, (y # ys)) qs), ?mat)"
      using False by simp
    then show ?thesis by simp
  qed
qed

(* cleansing preserves semantics *)
lemma pop_redundant_ex_prefix_var_semantics_eq:
  assumes "x \<in> set (pcnf_prefix_variables (prefix_pop (ExistentialFirst (x, xs) qs), matrix))"
  shows "pcnf_semantics I (ExistentialFirst (x, xs) qs, matrix)
        = pcnf_semantics I (prefix_pop (ExistentialFirst (x, xs) qs), matrix)"
proof -
  let ?pcnf = "(ExistentialFirst (x, xs) qs, matrix)"
  let ?pop = "(prefix_pop (ExistentialFirst (x, xs) qs), matrix)"
  have "set (pcnf_prefix_variables ?pcnf) = set (pcnf_prefix_variables ?pop)"
    using assms prefix_pop_ex_prefix_vars_set by auto
  hence "x \<notin> set (pcnf_free_variables ?pop)"
    using assms pcnf_free_eq_vars_minus_prefix by simp
  hence 0: "\<forall>z \<in> set (pcnf_free_variables ?pop). (I(x := b)) z = I z"
    for b by simp
  moreover have "pcnf_semantics I ?pcnf
       \<longleftrightarrow> pcnf_semantics (I(x := True)) ?pop
         \<or> pcnf_semantics (I(x := False)) ?pop"
    by (induction "ExistentialFirst (x, xs) qs" rule: prefix_pop.induct) auto
  ultimately show ?thesis using pcnf_semantics_eq_if_free_vars_eq by blast
qed

lemma pop_redundant_all_prefix_var_semantics_eq:
  assumes "y \<in> set (pcnf_prefix_variables (prefix_pop (UniversalFirst (y, ys) qs), matrix))"
  shows "pcnf_semantics I (UniversalFirst (y, ys) qs, matrix)
        = pcnf_semantics I (prefix_pop (UniversalFirst (y, ys) qs), matrix)"
proof -
  let ?pcnf = "(UniversalFirst (y, ys) qs, matrix)"
  let ?pop = "(prefix_pop (UniversalFirst (y, ys) qs), matrix)"
  have "set (pcnf_prefix_variables ?pcnf) = set (pcnf_prefix_variables ?pop)"
    using assms prefix_pop_all_prefix_vars_set by auto
  hence "y \<notin> set (pcnf_free_variables ?pop)"
    using assms pcnf_free_eq_vars_minus_prefix by simp
  hence 0: "\<forall>z \<in> set (pcnf_free_variables ?pop). (I(y := b)) z = I z"
    for b by simp
  moreover have "pcnf_semantics I ?pcnf
       \<longleftrightarrow> pcnf_semantics (I(y := True)) ?pop
         \<and> pcnf_semantics (I(y := False)) ?pop"
    by (induction "ExistentialFirst (y, ys) qs" rule: prefix_pop.induct) auto
  ultimately show ?thesis using pcnf_semantics_eq_if_free_vars_eq by blast
qed

lemma pcnf_semantics_disj_eq_add_ex:
  "pcnf_semantics (I(y := True)) pcnf \<or> pcnf_semantics (I(y := False)) pcnf
  \<longleftrightarrow> pcnf_semantics I (add_existential_to_front y pcnf)"
  using convert_add_ex qbf_semantics_eq_pcnf_semantics qbf_semantics_substitute_eq_assign by simp

lemma pcnf_semantics_conj_eq_add_all:
  "pcnf_semantics (I(y := True)) pcnf \<and> pcnf_semantics (I(y := False)) pcnf
  \<longleftrightarrow> pcnf_semantics I (add_universal_to_front y pcnf)"
  using convert_add_all qbf_semantics_eq_pcnf_semantics qbf_semantics_substitute_eq_assign by simp

theorem pcnf_cleanse_preserves_semantics:
  "pcnf_semantics I pcnf = pcnf_semantics I (pcnf_cleanse pcnf)"
proof (induction pcnf arbitrary: I rule: pcnf_cleanse.induct)
  case (1 matrix)
  then show ?case by simp
next
  case (2 y ys qs matrix)
  hence 0: "pcnf_semantics I (prefix_pop (UniversalFirst (y, ys) qs), matrix) =
    pcnf_semantics I (pcnf_cleanse (prefix_pop (UniversalFirst (y, ys) qs), matrix))"
    for I by cases auto
  show ?case
  proof (cases "y \<in> set (pcnf_prefix_variables (prefix_pop (UniversalFirst (y, ys) qs), matrix))")
    case True
    then show ?thesis
      using 0 pop_redundant_all_prefix_var_semantics_eq by simp
  next
    case False
    moreover have "pcnf_semantics I (UniversalFirst (y, ys) qs, matrix)
       \<longleftrightarrow> pcnf_semantics (I(y := True)) (prefix_pop (UniversalFirst (y, ys) qs), matrix)
         \<and> pcnf_semantics (I(y := False)) (prefix_pop (UniversalFirst (y, ys) qs), matrix)"
      by (induction "UniversalFirst (y, ys) qs" rule: prefix_pop.induct) auto
    ultimately show ?thesis using 0 pcnf_semantics_conj_eq_add_all by simp
  qed
next
  case (3 x xs qs matrix)
  hence 0: "pcnf_semantics I (prefix_pop (ExistentialFirst (x, xs) qs), matrix) =
    pcnf_semantics I (pcnf_cleanse (prefix_pop (ExistentialFirst (x, xs) qs), matrix))"
    for I by cases auto
  show ?case
  proof (cases "x \<in> set (pcnf_prefix_variables (prefix_pop (ExistentialFirst (x, xs) qs), matrix))")
    case True
    then show ?thesis
      using 0 pop_redundant_ex_prefix_var_semantics_eq by simp
  next
    case False
    moreover have "pcnf_semantics I (ExistentialFirst (x, xs) qs, matrix)
       \<longleftrightarrow> pcnf_semantics (I(x := True)) (prefix_pop (ExistentialFirst (x, xs) qs), matrix)
         \<or> pcnf_semantics (I(x := False)) (prefix_pop (ExistentialFirst (x, xs) qs), matrix)"
      by (induction "ExistentialFirst (x, xs) qs" rule: prefix_pop.induct) auto
    ultimately show ?thesis using 0 pcnf_semantics_disj_eq_add_ex by simp
  qed
qed

(* The satisfiability theorems can then be restated using cleansed formulas *)
theorem sat_ex_first_iff_assign_disj_sat':
  assumes "cleansed_p (ExistentialFirst (x, xs) qs, matrix)"
  shows "satisfiable (convert (ExistentialFirst (x, xs) qs, matrix))
  \<longleftrightarrow> satisfiable (Disj
    [convert (pcnf_assign (P x) (ExistentialFirst (x, xs) qs, matrix)),
     convert (pcnf_assign (N x) (ExistentialFirst (x, xs) qs, matrix))])"
  using assms cleansed_prefix_first_ex_unique sat_ex_first_iff_assign_disj_sat by auto

theorem sat_all_first_iff_assign_conj_sat':
  assumes "cleansed_p (UniversalFirst (y, ys) qs, matrix)"
  shows "satisfiable (convert (UniversalFirst (y, ys) qs, matrix))
  \<longleftrightarrow> satisfiable (Conj
    [convert (pcnf_assign (P y) (UniversalFirst (y, ys) qs, matrix)),
     convert (pcnf_assign (N y) (UniversalFirst (y, ys) qs, matrix))])"
  using assms cleansed_prefix_first_all_unique sat_all_first_iff_assign_conj_sat by auto

(* search based solver *)
lemma add_all_inc_prefix_measure:
  "prefix_measure (add_universal_to_prefix y prefix) = Suc (prefix_measure prefix)"
  by (induction y prefix rule: add_universal_to_prefix.induct) auto

lemma add_ex_inc_prefix_measure:
  "prefix_measure (add_existential_to_prefix x prefix) = Suc (prefix_measure prefix)"
  by (induction x prefix rule: add_universal_to_prefix.induct) auto

lemma remove_var_non_increasing_measure:
  "prefix_measure (remove_var_prefix z prefix) \<le> prefix_measure prefix"
proof (induction z prefix rule: remove_var_prefix.induct)
  case (1 x)
  then show ?case by simp
next
  case (2 x y ys qs)
  hence 0: "prefix_measure (remove_var_prefix x (prefix_pop (UniversalFirst (y, ys) qs)))
    \<le> prefix_measure (prefix_pop (UniversalFirst (y, ys) qs))"
  by (cases "x = y") (cases "prefix_pop (UniversalFirst (y, ys) qs) = Empty",simp_all)+
  show ?case
  proof (cases "x = y")
    case True
    hence "prefix_measure (remove_var_prefix x (UniversalFirst (y, ys) qs))
          = prefix_measure (remove_var_prefix x (prefix_pop (UniversalFirst (y, ys) qs)))" by simp
    also have "... \<le> prefix_measure (prefix_pop (UniversalFirst (y, ys) qs))" using 0 by simp
    also have "... \<le> prefix_measure (UniversalFirst (y, ys) qs)"
      using prefix_pop_decreases_measure less_imp_le_nat by blast
    finally show ?thesis .
  next
    case False
    hence "prefix_measure (remove_var_prefix x (UniversalFirst (y, ys) qs))
          = prefix_measure (add_universal_to_prefix y
              (remove_var_prefix x (prefix_pop (UniversalFirst (y, ys) qs))))" by simp
    also have "... \<le> Suc (prefix_measure (prefix_pop (UniversalFirst (y, ys) qs)))"
      using 0 add_all_inc_prefix_measure by simp
    also have "... \<le> prefix_measure (UniversalFirst (y, ys) qs)"
      using Suc_leI prefix_pop_decreases_measure by blast
    finally show ?thesis .
  qed
next
  case (3 x y ys qs)
  hence 0: "prefix_measure (remove_var_prefix x (prefix_pop (ExistentialFirst (y, ys) qs)))
    \<le> prefix_measure (prefix_pop (ExistentialFirst (y, ys) qs))"
  by (cases "x = y") (cases "prefix_pop (ExistentialFirst (y, ys) qs) = Empty",simp_all)+
  show ?case
  proof (cases "x = y")
    case True
    hence "prefix_measure (remove_var_prefix x (ExistentialFirst (y, ys) qs))
          = prefix_measure (remove_var_prefix x (prefix_pop (ExistentialFirst (y, ys) qs)))" by simp
    also have "... \<le> prefix_measure (prefix_pop (ExistentialFirst (y, ys) qs))" using 0 by simp
    also have "... \<le> prefix_measure (ExistentialFirst (y, ys) qs)"
      using le_eq_less_or_eq prefix_pop_decreases_measure by blast
    finally show ?thesis .
  next
    case False
    hence "prefix_measure (remove_var_prefix x (ExistentialFirst (y, ys) qs))
          = prefix_measure (add_existential_to_prefix y
              (remove_var_prefix x (prefix_pop (ExistentialFirst (y, ys) qs))))" by simp
    also have "... \<le> Suc (prefix_measure (prefix_pop (ExistentialFirst (y, ys) qs)))"
      using 0 add_ex_inc_prefix_measure by simp
    also have "... \<le> prefix_measure (ExistentialFirst (y, ys) qs)"
      using Suc_leI prefix_pop_decreases_measure by blast
    finally show ?thesis .
  qed
qed

fun first_var :: "prefix \<Rightarrow> nat option" where
"first_var (ExistentialFirst (x, xs) qs) = Some x" |
"first_var (UniversalFirst (y, ys) qs) = Some y" |
"first_var Empty = None"

lemma remove_first_var_decreases_measure:
  assumes "prefix \<noteq> Empty"
  shows "prefix_measure (remove_var_prefix (the (first_var prefix)) prefix) < prefix_measure prefix"
  using assms
proof (induction prefix)
  case (UniversalFirst q qs)
  then show ?case
  proof (induction q)
    case (Pair y ys)
    let ?pre = "UniversalFirst (y, ys) qs"
    let ?var = "the (first_var ?pre)"
    have "prefix_measure (remove_var_prefix ?var ?pre)
         \<le> prefix_measure (prefix_pop ?pre)"
      using remove_var_non_increasing_measure by simp
    also have "... < prefix_measure ?pre"
      using prefix_pop_decreases_measure by blast
    finally show ?case .
  qed
next
  case (ExistentialFirst q qs)
  then show ?case
  proof (induction q)
    case (Pair x xs)
    let ?pre = "ExistentialFirst (x, xs) qs"
    let ?var = "the (first_var ?pre)"
    have "prefix_measure (remove_var_prefix ?var ?pre)
         \<le> prefix_measure (prefix_pop ?pre)"
      using remove_var_non_increasing_measure by simp
    also have "... < prefix_measure ?pre"
      using prefix_pop_decreases_measure by blast
    finally show ?case .
  qed
next
  case Empty
  then show ?case by simp
qed

fun first_existential :: "prefix \<Rightarrow> bool option" where
"first_existential (ExistentialFirst q qs) = Some True" |
"first_existential (UniversalFirst q qs) = Some False" |
"first_existential Empty = None"

function search :: "pcnf \<Rightarrow> bool option" where
"search (prefix, matrix) =
  (if [] \<in> set matrix then Some False
  else if matrix = [] then Some True
  else Option.bind (first_var prefix) (\<lambda>z.
  Option.bind (first_existential prefix) (\<lambda>e. if e
    then combine_options (\<or>)
      (search (pcnf_assign (P z) (prefix, matrix)))
      (search (pcnf_assign (N z) (prefix, matrix)))
    else combine_options (\<and>)
      (search (pcnf_assign (P z) (prefix, matrix)))
      (search (pcnf_assign (N z) (prefix, matrix))))))"
  by pat_completeness auto
termination
  apply (relation "measure (\<lambda>(pre, mat). prefix_measure pre)")
  apply (auto simp add: prefix_pop_decreases_measure simp del: prefix_measure.simps)
  using remove_first_var_decreases_measure first_var.simps(3) option.discI option.sel by metis+

value "search (UniversalFirst (1, []) [(2, [3])], [])"
value "search (UniversalFirst (1, []) [(2, [3])], [[]])"
value "search (UniversalFirst (1, []) [(2, [3])], [[P 1]])"
value "search (UniversalFirst (1, []) [(2, [3])], [[P 1, N 2]])"
value "search (UniversalFirst (1, []) [(2, [3])], [[P 1, N 2], [N 1, P 3]])"

fun search_solver :: "pcnf \<Rightarrow> bool" where
"search_solver pcnf = the (search (pcnf_cleanse (pcnf_existential_closure pcnf)))"

value "search_solver (UniversalFirst (1, []) [(2, [3])], [])"
value "search_solver (UniversalFirst (1, []) [(2, [3])], [[]])"
value "search_solver (UniversalFirst (1, []) [(2, [3])], [[P 1]])"
value "search_solver (UniversalFirst (1, []) [(2, [3])], [[P 1, N 2]])"
value "search_solver (UniversalFirst (1, []) [(2, [3])], [[P 1, N 2], [N 1, P 3]])"
value "search_solver (UniversalFirst (1, []) [(2, [3])], [[P 1, N 2], [N 1, P 3], [P 4]])"
value "search_solver (UniversalFirst (1, []) [(2, [3, 3, 3])], [[P 1, N 2], [N 1, P 3], [P 4]])"

lemma search_cleansed_closed_yields_Some:
  assumes "cleansed_p pcnf" and "pcnf_free_variables pcnf = []"
  shows "(\<exists>b. search pcnf = Some b)" using assms
proof (induction pcnf rule: search.induct)
  case (1 prefix matrix)
  then show ?case
  proof (cases "[] \<in> set matrix")
    case True
    then show ?thesis by auto
  next
    case 2: False
    then show ?thesis
    proof (cases "matrix = []")
      case True
      then show ?thesis by auto
    next
      case 3: False
      then show ?thesis
      proof (cases "first_var prefix")
        case None
        hence "prefix = Empty" by (induction prefix) auto
        hence False using `matrix \<noteq> []` `[] \<notin> set matrix`
            `pcnf_free_variables (prefix, matrix) = []`
            empty_clause_or_matrix_if_no_variables
            no_vars_if_no_free_empty_prefix by blast
        then show ?thesis by simp
      next
        case 4: (Some z)
        then show ?thesis
        proof (cases "first_existential prefix")
          case None
          hence "prefix = Empty" by (induction prefix) auto
          hence False using `matrix \<noteq> []` `[] \<notin> set matrix`
              `pcnf_free_variables (prefix, matrix) = []`
              empty_clause_or_matrix_if_no_variables
              no_vars_if_no_free_empty_prefix by blast
          then show ?thesis by simp
        next
          case 5: (Some e)
          have 6: "pcnf_free_variables (pcnf_assign lit (prefix, matrix)) = []"
            for lit using pcnf_assign_free_subseteq_free_minus_lit 1(6)
              Diff_empty set_empty subset_Diff_insert subset_empty
              by metis
          then show ?thesis
          proof (cases e)
            case 7: True
            have "search (prefix, matrix)
                  = combine_options (\<or>)
                      (search (pcnf_assign (P z) (prefix, matrix)))
                      (search (pcnf_assign (N z) (prefix, matrix)))"
              using 2 3 4 5 7 by simp
            moreover have "\<exists>b. search (pcnf_assign (P z) (prefix, matrix)) = Some b"
              using 2 3 4 5 6 7 1(5,6) pcnf_assign_cleansed_inv 1(1)[of z e] by blast
            moreover have "\<exists>b. search (pcnf_assign (N z) (prefix, matrix)) = Some b"
              using 2 3 4 5 6 7 1(5,6) pcnf_assign_cleansed_inv 1(2)[of z e] by blast
            ultimately show ?thesis by force
          next
            case 7: False
            have "search (prefix, matrix)
                  = combine_options (\<and>)
                      (search (pcnf_assign (P z) (prefix, matrix)))
                      (search (pcnf_assign (N z) (prefix, matrix)))"
              using 2 3 4 5 7 by simp
            moreover have "\<exists>b. search (pcnf_assign (P z) (prefix, matrix)) = Some b"
              using 2 3 4 5 6 7 1(5,6) pcnf_assign_cleansed_inv 1(3)[of z e] by blast
            moreover have "\<exists>b. search (pcnf_assign (N z) (prefix, matrix)) = Some b"
              using 2 3 4 5 6 7 1(5,6) pcnf_assign_cleansed_inv 1(4)[of z e] by blast
            ultimately show ?thesis by force
          qed
        qed
      qed
    qed
  qed
qed

theorem search_cleansed_closed_correct:
  assumes "cleansed_p pcnf" and "pcnf_free_variables pcnf = []"
  shows "search pcnf = Some (satisfiable (convert pcnf))" using assms
proof (induction pcnf rule: search.induct)
  case (1 prefix matrix)
  then show ?case
  proof (cases "[] \<in> set matrix")
    case True
    then show ?thesis
      using false_if_empty_clause_in_matrix qbf_semantics_eq_pcnf_semantics satisfiable_def by simp
  next
    case 2: False
    then show ?thesis
    proof (cases "matrix = []")
      case True
      then show ?thesis
        using true_if_matrix_empty qbf_semantics_eq_pcnf_semantics satisfiable_def by simp
    next
      case 3: False
      then show ?thesis
      proof (cases "first_var prefix")
        case None
        hence "prefix = Empty" by (induction prefix) auto
        hence False using `matrix \<noteq> []` `[] \<notin> set matrix`
            `pcnf_free_variables (prefix, matrix) = []`
            empty_clause_or_matrix_if_no_variables
            no_vars_if_no_free_empty_prefix by blast
        then show ?thesis by simp
      next
        case 4: (Some z)
        then show ?thesis
        proof (cases "first_existential prefix")
          case None
          hence "prefix = Empty" by (induction prefix) auto
          hence False using `matrix \<noteq> []` `[] \<notin> set matrix`
              `pcnf_free_variables (prefix, matrix) = []`
              empty_clause_or_matrix_if_no_variables
              no_vars_if_no_free_empty_prefix by blast
          then show ?thesis by simp
        next
          case 5: (Some e)
          have 6: "pcnf_free_variables (pcnf_assign lit (prefix, matrix)) = []"
            for lit using pcnf_assign_free_subseteq_free_minus_lit 1(6)
              Diff_empty set_empty subset_Diff_insert subset_empty
            by metis
          hence 7: "\<exists>b. search (pcnf_assign lit (prefix, matrix)) = Some b" for lit
            using search_cleansed_closed_yields_Some pcnf_assign_cleansed_inv 6 1(5,6) by blast
          then show ?thesis
          proof (cases e)
            case 8: True
            from this obtain x xs qs where prefix_def: "prefix = ExistentialFirst (x, xs) qs"
              using 5 by (induction prefix) auto
            have "search (prefix, matrix)
                  = combine_options (\<or>)
                      (search (pcnf_assign (P z) (prefix, matrix)))
                      (search (pcnf_assign (N z) (prefix, matrix)))"
              using 2 3 4 5 8 by simp
            hence 9: "the (search (prefix, matrix))
                  \<longleftrightarrow> the (search (pcnf_assign (P z) (prefix, matrix)))
                    \<or> the (search (pcnf_assign (N z) (prefix, matrix)))"
              using 7 combine_options_simps(3) option.sel by metis
            have "search (pcnf_assign (P z) (prefix, matrix))
                 = Some (satisfiable (convert (pcnf_assign (P z) (prefix, matrix))))"
              using 2 3 4 5 6 8 1(5,6) pcnf_assign_cleansed_inv 1(1)[of z e] by blast
            moreover have "set (free_variables (convert (pcnf_assign (P z) (prefix, matrix)))) = {}"
              using 6[of "P z"] by simp
            ultimately have 10: "\<forall>I. the (search (pcnf_assign (P z) (prefix, matrix)))
                  = qbf_semantics I (convert (pcnf_assign (P z) (prefix, matrix)))"
              using semantics_eq_if_free_vars_eq[of "convert (pcnf_assign (P z) (prefix, matrix))"]
              by (auto simp add: satisfiable_def)
            have "search (pcnf_assign (N z) (prefix, matrix))
                 = Some (satisfiable (convert (pcnf_assign (N z) (prefix, matrix))))"
              using 2 3 4 5 6 8 1(5,6) pcnf_assign_cleansed_inv 1(2)[of z e] by blast
            moreover have "set (free_variables (convert (pcnf_assign (N z) (prefix, matrix)))) = {}"
              using 6[of "N z"] by simp
            ultimately have 11: "\<forall>I. the (search (pcnf_assign (N z) (prefix, matrix)))
                  = qbf_semantics I (convert (pcnf_assign (N z) (prefix, matrix)))"
              using semantics_eq_if_free_vars_eq[of "convert (pcnf_assign (N z) (prefix, matrix))"]
              by (auto simp add: satisfiable_def)
            have "the (search (prefix, matrix))
                 = satisfiable (Disj
                   [convert (pcnf_assign (P z) (prefix, matrix)),
                    convert (pcnf_assign (N z) (prefix, matrix))])"
              using 9 10 11 satisfiable_def by simp
            hence "search (prefix, matrix)
                 = Some (satisfiable (Disj
                   [convert (pcnf_assign (P z) (prefix, matrix)),
                    convert (pcnf_assign (N z) (prefix, matrix))]))"
              using 1(5,6) search_cleansed_closed_yields_Some by fastforce
            moreover have "z = x" using prefix_def 4 by simp
            ultimately show ?thesis using sat_ex_first_iff_assign_disj_sat' prefix_def 1(5) by simp
          next
            case 8: False
            from this obtain y ys qs where prefix_def: "prefix = UniversalFirst (y, ys) qs"
              using 5 by (induction prefix) auto
            have "search (prefix, matrix)
                  = combine_options (\<and>)
                      (search (pcnf_assign (P z) (prefix, matrix)))
                      (search (pcnf_assign (N z) (prefix, matrix)))"
              using 2 3 4 5 8 by simp
            hence 9: "the (search (prefix, matrix))
                  \<longleftrightarrow> the (search (pcnf_assign (P z) (prefix, matrix)))
                    \<and> the (search (pcnf_assign (N z) (prefix, matrix)))"
              using 7 combine_options_simps(3) option.sel by metis
            have "search (pcnf_assign (P z) (prefix, matrix))
                 = Some (satisfiable (convert (pcnf_assign (P z) (prefix, matrix))))"
              using 2 3 4 5 6 8 1(5,6) pcnf_assign_cleansed_inv 1(3)[of z e] by blast
            moreover have "set (free_variables (convert (pcnf_assign (P z) (prefix, matrix)))) = {}"
              using 6[of "P z"] by simp
            ultimately have 10: "\<forall>I. the (search (pcnf_assign (P z) (prefix, matrix)))
                  = qbf_semantics I (convert (pcnf_assign (P z) (prefix, matrix)))"
              using semantics_eq_if_free_vars_eq[of "convert (pcnf_assign (P z) (prefix, matrix))"]
              by (auto simp add: satisfiable_def)
            have "search (pcnf_assign (N z) (prefix, matrix))
                 = Some (satisfiable (convert (pcnf_assign (N z) (prefix, matrix))))"
              using 2 3 4 5 6 8 1(5,6) pcnf_assign_cleansed_inv 1(4)[of z e] by blast
            moreover have "set (free_variables (convert (pcnf_assign (N z) (prefix, matrix)))) = {}"
              using 6[of "N z"] by simp
            ultimately have 11: "\<forall>I. the (search (pcnf_assign (N z) (prefix, matrix)))
                  = qbf_semantics I (convert (pcnf_assign (N z) (prefix, matrix)))"
              using semantics_eq_if_free_vars_eq[of "convert (pcnf_assign (N z) (prefix, matrix))"]
              by (auto simp add: satisfiable_def)
            have "the (search (prefix, matrix))
                 = satisfiable (Conj
                   [convert (pcnf_assign (P z) (prefix, matrix)),
                    convert (pcnf_assign (N z) (prefix, matrix))])"
              using 9 10 11 satisfiable_def by simp
            hence "search (prefix, matrix)
                 = Some (satisfiable (Conj
                   [convert (pcnf_assign (P z) (prefix, matrix)),
                    convert (pcnf_assign (N z) (prefix, matrix))]))"
              using 1(5,6) search_cleansed_closed_yields_Some by fastforce
            moreover have "z = y" using prefix_def 4 by simp
            ultimately show ?thesis using sat_all_first_iff_assign_conj_sat' prefix_def 1(5) by simp
          qed
        qed
      qed
    qed
  qed
qed

theorem search_solver_correct:
  "search_solver pcnf \<longleftrightarrow> satisfiable (convert pcnf)"
proof -
  have "satisfiable (convert pcnf)
       = satisfiable (convert (pcnf_cleanse (pcnf_existential_closure pcnf)))"
    using pcnf_sat_iff_ex_close_sat pcnf_cleanse_preserves_semantics
      qbf_semantics_eq_pcnf_semantics satisfiable_def by simp
  moreover have "pcnf_free_variables (pcnf_cleanse (pcnf_existential_closure pcnf)) = []"
    using pcnf_ex_closure_no_free cleanse_free_vars_inv set_empty by metis
  moreover have "cleansed_p (pcnf_cleanse (pcnf_existential_closure pcnf))"
    using pcnf_cleanse_cleanses by blast
  ultimately show ?thesis using search_cleansed_closed_correct by simp
qed

end