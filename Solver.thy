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
  assumes "z \<in> set qbf_list"
  shows "qbf_measure z < Suc (sum_list (map qbf_measure qbf_list))"
proof -
  obtain left right where "left @ z # right = qbf_list" by (metis assms split_list)
  hence "sum_list (map qbf_measure qbf_list)
        = sum_list (map qbf_measure left) + qbf_measure z + sum_list (map qbf_measure right)"
    by fastforce
  thus "qbf_measure z < Suc (sum_list (map qbf_measure qbf_list))" by simp
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

(*** Conversion functions, left-inverses thereof, and proofs of the left-inverseness. ***)
(* Convert literal *)
fun convert_literal :: "literal \<Rightarrow> QBF" where
"convert_literal (P z) = Var z" |
"convert_literal (N z) = Neg (Var z)"

fun convert_literal_inv :: "QBF \<Rightarrow> literal option" where
"convert_literal_inv (Var z) = Some (P z)" |
"convert_literal_inv (Neg (Var z)) = Some (N z)" |
"convert_literal_inv _ = None"

lemma literal_inv: "convert_literal_inv (convert_literal n) = Some n"
proof (induction rule: convert_literal.induct)
  case (1 z)
  thus "convert_literal_inv (convert_literal (P z)) = Some (P z)" by simp
next
  case (2 z)
  thus "convert_literal_inv (convert_literal (N z)) = Some (N z)" by simp
qed

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
  proof (induction rule: convert.induct)
    case (1 matrix)
    show "convert_inv (convert (Empty, matrix)) = Some (Empty, matrix)"
      using matrix_inv by simp
  next
    case (2 x matrix)
    show "convert_inv (convert (UniversalFirst (x, []) [], matrix))
         = Some (UniversalFirst (x, []) [], matrix)"
      using matrix_inv by simp
  next
    case (3 x matrix)
    show "convert_inv (convert (ExistentialFirst (x, []) [], matrix))
         = Some (ExistentialFirst (x, []) [], matrix)"
      using matrix_inv by simp
  next
    case (4 x q qs matrix)
    moreover have "add_universal_to_front x (ExistentialFirst q qs, matrix)
                  = (UniversalFirst (x, []) (q # qs), matrix)"
      by (induction q) simp
    ultimately show "convert_inv (convert (UniversalFirst (x, []) (q # qs), matrix))
                    = Some (UniversalFirst (x, []) (q # qs), matrix)"
      by simp
  next
    case (5 x q qs matrix)
    moreover have "add_existential_to_front x (UniversalFirst q qs, matrix)
                  = (ExistentialFirst (x, []) (q # qs), matrix)"
      by (induction q) simp
    ultimately show "convert_inv (convert (ExistentialFirst (x, []) (q # qs), matrix))
                    = Some (ExistentialFirst (x, []) (q # qs), matrix)"
      by simp
  next
    case (6 x y ys qs matrix)
    moreover have "add_universal_to_front x (ExistentialFirst (y, ys) qs, matrix)
                  = (UniversalFirst (x, []) ((y, ys) # qs), matrix)"
      by simp
    ultimately show "convert_inv (convert (UniversalFirst (x, y # ys) qs, matrix))
                    = Some (UniversalFirst (x, y # ys) qs, matrix)"
      by simp
  next
    case (7 x y ys qs matrix)
    moreover have "add_existential_to_front x (UniversalFirst (y, ys) qs, matrix)
                  = (ExistentialFirst (x, []) ((y, ys) # qs), matrix)"
      by simp
    ultimately show "convert_inv (convert (ExistentialFirst (x, y # ys) qs, matrix))
                    = Some (ExistentialFirst (x, y # ys) qs, matrix)"
      by simp
  qed    
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
    moreover from Cons convert_literal_p_ex obtain y where "convert_literal y = x" by fastforce
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
    moreover from Cons convert_literal_p_ex obtain y where "convert_clause y = x" by fastforce
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
(* IDK, old stuff *)

(*
(* Old implementation, more difficult to create a provably correct left inverse for. *)
fun convert_quant_all :: "quant_set \<Rightarrow> QBF \<Rightarrow> QBF" where
"convert_quant_all (x, []) qbf = All x qbf" |
"convert_quant_all (x, (y # ys)) qbf = All x (convert_quant_all (y, ys) qbf)"

fun convert_quant_ex :: "quant_set \<Rightarrow> QBF \<Rightarrow> QBF" where
"convert_quant_ex (x, []) qbf = Ex x qbf" |
"convert_quant_ex (x, (y # ys)) qbf = Ex x (convert_quant_ex (y, ys) qbf)"

fun convert_aux :: "bool \<Rightarrow> quant_sets \<Rightarrow> matrix \<Rightarrow> QBF" where
"convert_aux _ [] matrix = convert_matrix matrix" |
"convert_aux True (q # qs) matrix = convert_quant_all q (convert_aux False qs matrix)" |
"convert_aux False (q # qs) matrix = convert_quant_ex q (convert_aux True qs matrix)"

fun convert :: "pcnf \<Rightarrow> QBF" where
"convert (UniversalFirst q qs, matrix) = convert_aux False (q # qs) matrix" |
"convert (ExistentialFirst q qs, matrix) = convert_aux True (q # qs) matrix" |
"convert (Empty, matrix) = convert_matrix matrix"

fun rev_quant_set :: "'a \<times> 'a list \<Rightarrow> 'a \<times> 'a list" where
"rev_quant_set (x, xs) = (let r = rev (x # xs) in (hd r, tl r))"

theorem rev_rev_quant_set: "rev_quant_set (rev_quant_set q) = q"
  by (induction q) (auto simp add: Let_def)

fun reverse_prefix :: "prefix \<Rightarrow> prefix" where
"reverse_prefix Empty = Empty" |
"reverse_prefix (UniversalFirst x xs) =
  (let r = rev (map rev_quant_set (x # xs))
   in if even (length r)
        then (ExistentialFirst (hd r) (tl r))
        else (UniversalFirst (hd r) (tl r)))" |
"reverse_prefix (ExistentialFirst x xs) =
  (let r = rev (map rev_quant_set (x # xs))
   in if even (length r)
        then (UniversalFirst (hd r) (tl r))
        else (ExistentialFirst (hd r) (tl r)))"

fun convert_alt_inv_aux :: "QBF \<Rightarrow> prefix \<Rightarrow> pcnf option" where
"convert_alt_inv_aux (All x qbf) Empty = convert_alt_inv_aux qbf (UniversalFirst (x, []) [])" |
"convert_alt_inv_aux (Ex x qbf) Empty = convert_alt_inv_aux qbf (ExistentialFirst (x, []) [])" |
"convert_alt_inv_aux (All x qbf) (UniversalFirst (y, ys) qs) =
  convert_alt_inv_aux qbf (UniversalFirst (x, y # ys) qs)" |
"convert_alt_inv_aux (Ex x qbf) (UniversalFirst (y, ys) qs) =
  convert_alt_inv_aux qbf (ExistentialFirst (x, []) (rev_quant_set (y, ys) # qs))" |
"convert_alt_inv_aux (All x qbf) (ExistentialFirst (y, ys) qs) =
  convert_alt_inv_aux qbf Empty
(*  convert_alt_inv_aux qbf (UniversalFirst (x, []) (rev_quant_set (y, ys) # qs))" |*)
"convert_alt_inv_aux (Ex x qbf) (ExistentialFirst (y, ys) qs) =
  convert_alt_inv_aux qbf (ExistentialFirst (x, y # ys) qs)" |
"convert_alt_inv_aux qbf Empty = map_option (\<lambda>x. (Empty, x)) (convert_matrix_inv qbf)" |
"convert_alt_inv_aux qbf (UniversalFirst q qs) =
  map_option (\<lambda>x. (UniversalFirst (rev_quant_set q) qs, x)) (convert_matrix_inv qbf)" |
"convert_alt_inv_aux qbf (ExistentialFirst q qs) =
  map_option (\<lambda>x. (ExistentialFirst (rev_quant_set q) qs, x)) (convert_matrix_inv qbf)"


fun convert_alt_inv :: "QBF \<Rightarrow> pcnf option" where
"convert_alt_inv qbf = convert_alt_inv_aux qbf Empty"

value "convert_alt (UniversalFirst (0, []) [(0, [])], [])"

theorem convert_inv: "convert_alt_inv (convert_alt pcnf) = Some pcnf"
*)

(*
(* pcnf_p after conversion proof: *)
lemma pcnf_convert_quant_all: "pcnf_p qbf \<Longrightarrow> pcnf_p (convert_quant_all (x, ys) qbf)"
  apply (induction qbf rule: convert_quant_all.induct)
  by auto

lemma pcnf_convert_quant_ex: "pcnf_p qbf \<Longrightarrow> pcnf_p (convert_quant_ex (x, ys) qbf)"
  apply (induction qbf rule: convert_quant_ex.induct)
  by auto

lemma cnf_convert_matrix: "cnf_p (convert_matrix matrix)"
proof (induction matrix)
  case Nil
  show "cnf_p (convert_matrix [])" by simp
next
  case (Cons cl matrix)
  hence "list_all clause_p (map convert_clause matrix)" by simp
  moreover have "clause_p (convert_clause cl)"
  proof (induction cl)
    case Nil
    show "clause_p (convert_clause [])" by simp
  next
    case (Cons lit cl)
    hence "list_all literal_p (map convert_literal cl)" by simp
    moreover have "literal_p (convert_literal lit)"
      by (induction rule: convert_literal.induct) auto
    ultimately show "clause_p (convert_clause (lit # cl))" by simp
  qed
  ultimately show "cnf_p (convert_matrix (cl # matrix))" by simp
qed

lemma pcnf_convert_aux: "pcnf_p (convert_aux all quants matrix)"
proof (induction all quants matrix rule: convert_aux.induct)
  case (1 all matrix)
  show "pcnf_p (convert_aux all [] matrix)" using cnf_convert_matrix by simp
next
  case (2 q qs matrix)
  show "pcnf_p (convert_aux True (q # qs) matrix)"
  proof (cases q)
    case (Pair a b)
    thus ?thesis using 2 pcnf_convert_quant_all by simp
  qed
next
  case (3 q qs matrix)
  show "pcnf_p (convert_aux False (q # qs) matrix)"
  proof (cases q)
    case (Pair a b)
    thus ?thesis using 3 pcnf_convert_quant_ex by simp
  qed
qed

theorem pcnf_convert: "pcnf_p (convert pcnf)"
proof (induction rule: convert.induct)
  case (1 q qs matrix)
  have "pcnf_p (convert (UniversalFirst q qs, matrix)) = pcnf_p (convert_aux False (q # qs) matrix)"
    by simp
  thus "pcnf_p (convert (UniversalFirst q qs, matrix))" using pcnf_convert_aux by fastforce
next
  case (2 q qs matrix)
  have "pcnf_p (convert (ExistentialFirst q qs, matrix)) = pcnf_p (convert_aux True (q # qs) matrix)"
    by simp
  thus "pcnf_p (convert (ExistentialFirst q qs, matrix))" using pcnf_convert_aux by fastforce
next
  case (3 matrix)
  thus "pcnf_p (convert (Empty, matrix))" using cnf_convert_matrix by simp
qed

fun reverse_prefix :: "prefix \<Rightarrow> prefix" where
"reverse_prefix Empty = Empty" |
"reverse_prefix (UniversalFirst x xs) =
  (let r = rev (x # xs)
   in if even (length r)
        then (ExistentialFirst (hd r) (tl r))
        else (UniversalFirst (hd r) (tl r)))" |
"reverse_prefix (ExistentialFirst x xs) =
  (let r = rev (x # xs)
   in if even (length r)
        then (UniversalFirst (hd r) (tl r))
        else (ExistentialFirst (hd r) (tl r)))"

theorem reverse_reverse_prefix: "reverse_prefix (reverse_prefix prefix) = prefix"
proof (induction rule: reverse_prefix.induct)
  case 1
  show "reverse_prefix (reverse_prefix Empty) = Empty" by simp
next
  case (2 x xs)
  show "reverse_prefix (reverse_prefix (UniversalFirst x xs)) = UniversalFirst x xs"
    by (cases "even (length (x # xs))") (auto simp add: Let_def)
next
  case (3 x xs)
  show "reverse_prefix (reverse_prefix (ExistentialFirst x xs)) = ExistentialFirst x xs"
    by (cases "even (length (x # xs))") (auto simp add: Let_def)
qed

(* Returns (reversed prefix, remaining qbf) tuple. *)
fun convert_inv_prefix_aux :: "QBF \<Rightarrow> prefix \<Rightarrow> (prefix \<times> QBF)" where
"convert_inv_prefix_aux (All y qbf) (UniversalFirst (q_hd, q_tl) qs) =
  convert_inv_prefix_aux qbf (UniversalFirst (y, q_hd # q_tl) qs)" |
"convert_inv_prefix_aux (All y qbf) (ExistentialFirst (q_hd, q_tl) qs) =
  convert_inv_prefix_aux qbf (UniversalFirst (y, []) ((q_hd, q_tl) # qs))" |
"convert_inv_prefix_aux (Ex x qbf) (ExistentialFirst (q_hd, q_tl) qs) =
  convert_inv_prefix_aux qbf (ExistentialFirst (x, q_hd # q_tl) qs)" |
"convert_inv_prefix_aux (Ex x qbf) (UniversalFirst (q_hd, q_tl) qs) =
  convert_inv_prefix_aux qbf (ExistentialFirst (x, []) ((q_hd, q_tl) # qs))" |
"convert_inv_prefix_aux (All y qbf) Empty =
  convert_inv_prefix_aux qbf (UniversalFirst (y, []) [])" |
"convert_inv_prefix_aux (Ex x qbf) Empty =
  convert_inv_prefix_aux qbf (ExistentialFirst (x, []) [])" |
"convert_inv_prefix_aux qbf prefix = (prefix, qbf)"

fun convert_inv_prefix :: "QBF \<Rightarrow> (prefix \<times> QBF)" where
"convert_inv_prefix qbf = (let (p, q) = convert_inv_prefix_aux qbf Empty in (reverse_prefix p, q))"

fun tmp :: "nat \<Rightarrow> nat option" where
"tmp n = (if even n then Some n else None)"

value "list_ex (\<lambda>x. x = None) (map tmp [2, 3, 4])"

(*
fun convert_inv_clause :: "QBF list \<Rightarrow> clause option" where
"convert_inv_clause [] = Some []" |
"convert_inv_clause (Cons (Var n) xs) =
  map_option (\<lambda>xs. (pnum_num n) # xs) (convert_inv_clause xs)" |
"convert_inv_clause (Cons (Neg (Var n)) xs) =
  map_option (\<lambda>xs. (pnum_neg_num n) # xs) (convert_inv_clause xs)" |
"convert_inv_clause (Cons _ _) = None"

fun convert_inv_clause :: "QBF list \<Rightarrow> clause \<Rightarrow> clause option" where
"convert_inv_clause [] cl = Some cl" |
"convert_inv_clause (Cons (Var n) xs) cl = convert_inv_clause xs ((pnum_num n) # cl)" |
"convert_inv_clause (Cons (Neg (Var n)) xs) cl = convert_inv_clause xs ((pnum_neg_num n) # cl)" |
"convert_inv_clause (Cons _ _) _ = None"

fun convert_inv_clauses :: "QBF list \<Rightarrow> matrix \<Rightarrow> matrix option" where
"convert_inv_matrix_aux [] matrix = Some matrix" |
"convert_inv_matrix_aux (Cons (Disj literals) xs) matrix =
  (case convert_inv_clause literals of
     None \<Rightarrow> None |
     Some cl \<Rightarrow> convert_inv_clauses xs (cl # matrix))"
   

fun convert_inv_matrix :: "QBF \<Rightarrow> matrix option" where
"convert_inv_matrix (Conj clauses) = let clause_option = map " |
"convert_inv_matrix _ = None"

fun convert_inv :: "QBF \<Rightarrow> pcnf option" where
*)
*)

end