$( yapeano.mm

#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
            Metamath source file for Peano arithmetic
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#

                           ~~ PUBLIC DOMAIN ~~
This work is waived of all rights, including copyright, according to the CC0
Public Domain Dedication.  http://creativecommons.org/publicdomain/zero/1.0/

The predicate logic in the first part of this file is copied from "set.mm",
by Norman Megill and others.  See the header on that file for more details.

$)

$(
###############################################################################
            CLASSICAL FIRST ORDER LOGIC WITH EQUALITY
###############################################################################
$)

$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
                           Pre-logic
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)

  $( Declare the primitive constant symbols for propositional calculus. $)
  $c ( $.  $( Left parenthesis $)
  $c ) $.  $( Right parenthesis $)
  $c -> $. $( Right arrow (read:  "implies") $)
  $c -. $. $( Right handle (read:  "not") $)
  $c wff $. $( Well-formed formula symbol (read:  "the following symbol
               sequence is a wff") $)
  $c |- $. $( Turnstile (read:  "the following symbol sequence is provable" or
              'a proof exists for") $)

  $( wff variable sequence:  ph ps ch th ta et ze si rh mu la ka $)
  $( Introduce some variable names we will use to represent well-formed
     formulas (wff's). $)
  $v ph $.  $( Greek phi $)
  $v ps $.  $( Greek psi $)
  $v ch $.  $( Greek chi $)
  $v th $.  $( Greek theta $)
  $v ta $.  $( Greek tau $)
  $v et $.  $( Greek eta $)
  $v ze $.  $( Greek zeta $)
  $v si $.  $( Greek sigma $)
  $v rh $.  $( Greek rho $)
  $v mu $.  $( Greek mu $)
  $v la $.  $( Greek lambda $)
  $v ka $.  $( Greek kappa $)

  $( Specify some variables that we will use to represent wff's.
     The fact that a variable represents a wff is relevant only to a theorem
     referring to that variable, so we may use $f hypotheses.  The symbol
     ` wff ` specifies that the variable that follows it represents a wff. $)
  $( Let variable ` ph ` be a wff. $)
  wph $f wff ph $.
  $( Let variable ` ps ` be a wff. $)
  wps $f wff ps $.
  $( Let variable ` ch ` be a wff. $)
  wch $f wff ch $.
  $( Let variable ` th ` be a wff. $)
  wth $f wff th $.
  $( Let variable ` ta ` be a wff. $)
  wta $f wff ta $.
  $( Let variable ` et ` be a wff. $)
  wet $f wff et $.
  $( Let variable ` ze ` be a wff. $)
  wze $f wff ze $.
  $( Let variable ` si ` be a wff. $)
  wsi $f wff si $.
  $( Let variable ` rh ` be a wff. $)
  wrh $f wff rh $.
  $( Let variable ` mu ` be a wff. $)
  wmu $f wff mu $.
  $( Let variable ` la ` be a wff. $)
  wla $f wff la $.
  $( Let variable ` ka ` be a wff. $)
  wka $f wff ka $.

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                 Inferences for assisting proof development
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    dummylink.1 $e |- ph $.
    dummylink.2 $e |- ps $.
    $( (_Note_:  This inference rule and the next one, ~ idi , will normally
       never appear in a completed proof.  It can be ignored if you are using
       this database to assist learning logic - please start with the statement
       ~ wn instead.)

       This is a technical inference to assist proof development.  It provides
       a temporary way to add an independent subproof to a proof under
       development, for later assignment to a normal proof step.

       The metamath program's Proof Assistant requires proofs to be developed
       backwards from the conclusion with no gaps, and it has no mechanism that
       lets the user to work on isolated subproofs.  This inference provides a
       workaround for this limitation.  It can be inserted at any point in a
       proof to allow an independent subproof to be developed on the side, for
       later use as part of the final proof.

       _Instructions_:  (1) Assign this inference to any unknown step in the
       proof.  Typically, the last unknown step is the most convenient, since
       'assign last' can be used.  This step will be replicated in hypothesis
       dummylink.1, from where the development of the main proof can continue.
       (2) Develop the independent subproof backwards from hypothesis
       dummylink.2.  If desired, use a 'let' command to pre-assign the
       conclusion of the independent subproof to dummylink.2.  (3) After the
       independent subproof is complete, use 'improve all' to assign it
       automatically to an unknown step in the main proof that matches it.  (4)
       After the entire proof is complete, use 'minimize *' to clean up
       (discard) all dummylink references automatically.

       This inference was originally designed to assist importing partially
       completed Proof Worksheets from the mmj2 Proof Assistant GUI, but it can
       also be useful on its own.  Interestingly, no axioms are required for
       its proof. $)
    dummylink $p |- ph $=
      (  ) C $.
      $( [7-Feb-2006] $)
  $}

  ${
    idi.1 $e |- ph $.
    $( Inference form of ~ id .  This inference rule, which requires no axioms
       for its proof, is useful as a copy-paste mechanism during proof
       development in mmj2.  It is normally not referenced in the final version
       of a proof, since it is always redundant and can be removed using the
       'minimize *' command in the metamath program's Proof Assistant.
       (Contributed by Alan Sare, 31-Dec-2011.) $)
    idi $p |- ph $=
      (  ) B $.
      $( [31-Dec-2011] $)
  $}

$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
                           Propositional calculus
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Recursively define primitive wffs for propositional calculus
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( If ` ph ` is a wff, so is ` -. ph ` or "not ` ph ` ."  Part of the
     recursive definition of a wff (well-formed formula).  In classical logic
     (which is our logic), a wff is interpreted as either true or false.  So if
     ` ph ` is true, then ` -. ph ` is false; if ` ph ` is false, then
     ` -. ph ` is true.  Traditionally, Greek letters are used to represent
     wffs, and we follow this convention.  In propositional calculus, we define
     only wffs built up from other wffs, i.e. there is no starting or "atomic"
     wff.  Later, in predicate calculus, we will extend the basic wff
     definition by including atomic wffs ( ~ weq and ~ wel ). $)
  wn $a wff -. ph $.

  $( If ` ph ` and ` ps ` are wff's, so is ` ( ph -> ps ) ` or " ` ph ` implies
     ` ps ` ."  Part of the recursive definition of a wff.  The resulting wff
     is (interpreted as) false when ` ph ` is true and ` ps ` is false; it is
     true otherwise.  (Think of the truth table for an OR gate with input
     ` ph ` connected through an inverter.)  The left-hand wff is called the
     antecedent, and the right-hand wff is called the consequent.  In the case
     of ` ( ph -> ( ps -> ch ) ) ` , the middle ` ps ` may be informally called
     either an antecedent or part of the consequent depending on context. $)
  wi $a wff ( ph -> ps ) $.

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        The axioms of propositional calculus
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $(
     Postulate the three axioms of classical propositional calculus.
  $)

  $( Axiom _Simp_.  Axiom A1 of [Margaris] p. 49.  One of the 3 axioms of
     propositional calculus.  The 3 axioms are also given as Definition 2.1 of
     [Hamilton] p. 28.  This axiom is called _Simp_ or "the principle of
     simplification" in _Principia Mathematica_ (Theorem *2.02 of
     [WhiteheadRussell] p. 100) because "it enables us to pass from the joint
     assertion of ` ph ` and ` ps ` to the assertion of ` ph ` simply."

     _General remarks_:  Propositional calculus (axioms ~ ax-1 through ~ ax-3
     and rule ~ ax-mp ) can be thought of as asserting formulas that are
     universally "true" when their variables are replaced by any combination of
     "true" and "false."  Propositional calculus was first formalized by Frege
     in 1879, using as his axioms (in addition to rule ~ ax-mp ) the wffs
     ~ ax-1 , ~ ax-2 , ~ pm2.04 , ~ con3 , ~ notnot2 , and ~ notnot1 .  Around
     1930, Lukasiewicz simplified the system by eliminating the third (which
     follows from the first two, as you can see by looking at the proof of
     ~ pm2.04 ) and replacing the last three with our ~ ax-3 .  (Thanks to Ted
     Ulrich for this information.)

     The theorems of propositional calculus are also called _tautologies_.
     Tautologies can be proved very simply using truth tables, based on the
     true/false interpretation of propositional calculus.  To do this, we
     assign all possible combinations of true and false to the wff variables
     and verify that the result (using the rules described in ~ wi and ~ wn )
     always evaluates to true.  This is called the _semantic_ approach.  Our
     approach is called the _syntactic_ approach, in which everything is
     derived from axioms.  A metatheorem called the Completeness Theorem for
     Propositional Calculus shows that the two approaches are equivalent and
     even provides an algorithm for automatically generating syntactic proofs
     from a truth table.  Those proofs, however, tend to be long, since truth
     tables grow exponentially with the number of variables, and the much
     shorter proofs that we show here were found manually. $)
  ax-1 $a |- ( ph -> ( ps -> ph ) ) $.

  $( Axiom _Frege_.  Axiom A2 of [Margaris] p. 49.  One of the 3 axioms of
     propositional calculus.  It "distributes" an antecedent over two
     consequents.  This axiom was part of Frege's original system and is known
     as _Frege_ in the literature.  It is also proved as Theorem *2.77 of
     [WhiteheadRussell] p. 108.  The other direction of this axiom also turns
     out to be true, as demonstrated by ~ pm5.41 . $)
  ax-2 $a |- ( ( ph -> ( ps -> ch ) ) -> ( ( ph -> ps ) -> ( ph -> ch ) ) ) $.

  $( Axiom _Transp_.  Axiom A3 of [Margaris] p. 49.  One of the 3 axioms of
     propositional calculus.  It swaps or "transposes" the order of the
     consequents when negation is removed.  An informal example is that the
     statement "if there are no clouds in the sky, it is not raining" implies
     the statement "if it is raining, there are clouds in the sky."  This axiom
     is called _Transp_ or "the principle of transposition" in _Principia
     Mathematica_ (Theorem *2.17 of [WhiteheadRussell] p. 103).  We will also
     use the term "contraposition" for this principle, although the reader is
     advised that in the field of philosophical logic, "contraposition" has a
     different technical meaning. $)
  ax-3 $a |- ( ( -. ph -> -. ps ) -> ( ps -> ph ) ) $.

  $(
     Postulate the modus ponens rule of inference.
  $)

  ${
    $( Minor premise for modus ponens. $)
    min $e |- ph $.
    $( Major premise for modus ponens. $)
    maj $e |- ( ph -> ps ) $.
    $( Rule of Modus Ponens.  The postulated inference rule of propositional
       calculus.  See e.g.  Rule 1 of [Hamilton] p. 73.  The rule says, "if
       ` ph ` is true, and ` ph ` implies ` ps ` , then ` ps ` must also be
       true."  This rule is sometimes called "detachment," since it detaches
       the minor premise from the major premise.

       Note:  In some web page displays such as the Statement List, the symbols
       "&" and "=>" informally indicate the relationship between the hypotheses
       and the assertion (conclusion), abbreviating the English words "and" and
       "implies."  They are not part of the formal language. $)
    ax-mp $a |- ps $.
  $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Logical implication
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

$( The results in this section are based on implication only, and avoid ax-3.
   In an implication, the wff before the arrow is called the "antecedent" and
   the wff after the arrow is called the "consequent." $)

$( We will use the following descriptive terms very loosely:  A "closed form"
   or "tautology" has no $e hypotheses.  An "inference" has one or more $e
   hypotheses.  A "deduction" is an inference in which the hypotheses and the
   conclusion share the same antecedent. $)

  ${
    mp2b.1 $e |- ph $.
    mp2b.2 $e |- ( ph -> ps ) $.
    mp2b.3 $e |- ( ps -> ch ) $.
    $( A double modus ponens inference.  (Contributed by Mario Carneiro,
       24-Jan-2013.) $)
    mp2b $p |- ch $=
      ( ax-mp ) BCABDEGFG $.
      $( [24-Jan-2013] $)
  $}

  ${
    $( Premise for ~ a1i . $)
    a1i.1 $e |- ph $.
    $( Inference derived from axiom ~ ax-1 .  See ~ a1d for an explanation of
       our informal use of the terms "inference" and "deduction."  See also the
       comment in ~ syld . $)
    a1i $p |- ( ps -> ph ) $=
      ( wi ax-1 ax-mp ) ABADCABEF $.
      $( [5-Aug-1993] $)
  $}

  ${
    $( Premise for ~ a2i . $)
    a2i.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Inference derived from axiom ~ ax-2 . $)
    a2i $p |- ( ( ph -> ps ) -> ( ph -> ch ) ) $=
      ( wi ax-2 ax-mp ) ABCEEABEACEEDABCFG $.
      $( [5-Aug-1993] $)
  $}

  ${
    imim2i.1 $e |- ( ph -> ps ) $.
    $( Inference adding common antecedents in an implication. $)
    imim2i $p |- ( ( ch -> ph ) -> ( ch -> ps ) ) $=
      ( wi a1i a2i ) CABABECDFG $.
      $( [5-Aug-1993] $)
  $}

  ${
    mpd.1 $e |- ( ph -> ps ) $.
    mpd.2 $e |- ( ph -> ( ps -> ch ) ) $.
    $( A modus ponens deduction. $)
    mpd $p |- ( ph -> ch ) $=
      ( wi a2i ax-mp ) ABFACFDABCEGH $.
      $( [5-Aug-1993] $)
  $}

  ${
    $( First of 2 premises for ~ syl . $)
    syl.1 $e |- ( ph -> ps ) $.
    $( Second of 2 premises for ~ syl . $)
    syl.2 $e |- ( ps -> ch ) $.
    $( An inference version of the transitive laws for implication ~ imim2 and
       ~ imim1 , which Russell and Whitehead call "the principle of the
       syllogism...because...the syllogism in Barbara is derived from them"
       (quote after Theorem *2.06 of [WhiteheadRussell] p. 101).  Some authors
       call this law a "hypothetical syllogism."  (The proof was shortened by
       O'Cat, 20-Oct-2011.)  (The proof was shortened by Wolf Lammen,
       26-Jul-2012.)

       (A bit of trivia: this is the most commonly referenced assertion in our
       database.  In second place is ~ ax-mp , followed by ~ vex , ~ bitri ,
       ~ imp , and ~ ex .  The Metamath program command 'show usage' shows the
       number of references.) $)
    syl $p |- ( ph -> ch ) $=
      ( wi a1i mpd ) ABCDBCFAEGH $.
      $( [27-Jul-2012] $) $( [5-Aug-1993] $)
  $}

  ${
    mpi.1 $e |- ps $.
    mpi.2 $e |- ( ph -> ( ps -> ch ) ) $.
    $( A nested modus ponens inference.  (The proof was shortened by Stefan
       Allan, 20-Mar-2006.) $)
    mpi $p |- ( ph -> ch ) $=
      ( a1i mpd ) ABCBADFEG $.
      $( [20-Mar-2006] $) $( [5-Aug-1993] $)
  $}

  ${
    mp2.1 $e |- ph $.
    mp2.2 $e |- ps $.
    mp2.3 $e |- ( ph -> ( ps -> ch ) ) $.
    $( A double modus ponens inference.  (The proof was shortened by Wolf
       Lammen, 23-Jul-2013.) $)
    mp2 $p |- ch $=
      ( mpi ax-mp ) ACDABCEFGH $.
      $( [23-Jul-2013] $) $( [5-Apr-1994] $)
  $}

  ${
    3syl.1 $e |- ( ph -> ps ) $.
    3syl.2 $e |- ( ps -> ch ) $.
    3syl.3 $e |- ( ch -> th ) $.
    $( Inference chaining two syllogisms. $)
    3syl $p |- ( ph -> th ) $=
      ( syl ) ACDABCEFHGH $.
      $( [5-Aug-1993] $)
  $}

  $( Principle of identity.  Theorem *2.08 of [WhiteheadRussell] p. 101.  For
     another version of the proof directly from axioms, see ~ id1 .  (The proof
     was shortened by Stefan Allan, 20-Mar-2006.) $)
  id $p |- ( ph -> ph ) $=
    ( wi ax-1 mpd ) AAABZAAACAECD $.
    $( [20-Mar-2006] $)

  $( Principle of identity.  Theorem *2.08 of [WhiteheadRussell] p. 101.  This
     version is proved directly from the axioms for demonstration purposes.
     This proof is a popular example in the literature and is identical, step
     for step, to the proofs of Theorem 1 of [Margaris] p. 51, Example 2.7(a)
     of [Hamilton] p. 31, Lemma 10.3 of [BellMachover] p. 36, and Lemma 1.8 of
     [Mendelson] p. 36.  It is also "Our first proof" in Hirst and Hirst's _A
     Primer for Logic and Proof_ p. 17 (PDF p. 23) at
     ~ http://www.mathsci.appstate.edu/~~jlh/primer/hirst.pdf .  For a shorter
     version of the proof that takes advantage of previously proved theorems,
     see ~ id . $)
  id1 $p |- ( ph -> ph ) $=
    ( wi ax-1 ax-2 ax-mp ) AAABZBZFAACAFABBGFBAFCAFADEE $.
    $( [5-Aug-1993] $)

  $( Principle of identity with antecedent. $)
  idd $p |- ( ph -> ( ps -> ps ) ) $=
    ( wi id a1i ) BBCABDE $.
    $( [26-Nov-1995] $)

  ${
    a1d.1 $e |- ( ph -> ps ) $.
    $( Deduction introducing an embedded antecedent.  (The proof was revised by
       Stefan Allan, 20-Mar-2006.)

       _Naming convention_:  We often call a theorem a "deduction" and suffix
       its label with "d" whenever the hypotheses and conclusion are each
       prefixed with the same antecedent.  This allows us to use the theorem in
       places where (in traditional textbook formalizations) the standard
       Deduction Theorem would be used; here ` ph ` would be replaced with a
       conjunction ( ~ df-an ) of the hypotheses of the would-be deduction.  By
       contrast, we tend to call the simpler version with no common antecedent
       an "inference" and suffix its label with "i"; compare theorem ~ a1i .
       Finally, a "theorem" would be the form with no hypotheses; in this case
       the "theorem" form would be the original axiom ~ ax-1 .  We usually show
       the theorem form without a suffix on its label (e.g. ~ pm2.43 vs.
       ~ pm2.43i vs. ~ pm2.43d ).  When an inference is converted to a theorem
       by eliminating an "is a set" hypothesis, we sometimes suffix the theorem
       form with "g" (for "more general") as in ~ uniex vs. ~ uniexg . $)
    a1d $p |- ( ph -> ( ch -> ps ) ) $=
      ( wi ax-1 syl ) ABCBEDBCFG $.
      $( [20-Mar-2006] $) $( [5-Aug-1993] $)
  $}

  ${
    a2d.1 $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
    $( Deduction distributing an embedded antecedent. $)
    a2d $p |- ( ph -> ( ( ps -> ch ) -> ( ps -> th ) ) ) $=
      ( wi ax-2 syl ) ABCDFFBCFBDFFEBCDGH $.
      $( [23-Jun-1994] $)
  $}

  ${
    a1ii.1 $e |- ch $.
    $( Add two antecedents to a wff.  (Contributed by Jeff Hankins,
       4-Aug-2009.)  (The proof was shortened by Wolf Lammen, 23-Jul-2013.) $)
    a1ii $p |- ( ph -> ( ps -> ch ) ) $=
      ( a1i a1d ) ACBCADEF $.
      $( [23-Jul-2013] $) $( [4-Aug-2009] $)
  $}

  ${
    sylcom.1 $e |- ( ph -> ( ps -> ch ) ) $.
    sylcom.2 $e |- ( ps -> ( ch -> th ) ) $.
    $( Syllogism inference with commutation of antecedents.  (The proof was
       shortened by O'Cat, 2-Feb-2006.)  (The proof was shortened by Stefan
       Allan, 23-Feb-2006.) $)
    sylcom $p |- ( ph -> ( ps -> th ) ) $=
      ( wi a2i syl ) ABCGBDGEBCDFHI $.
      $( [23-Feb-2006] $) $( [29-Aug-2004] $)
  $}

  ${
    syl5com.1 $e |- ( ph -> ps ) $.
    syl5com.2 $e |- ( ch -> ( ps -> th ) ) $.
    $( Syllogism inference with commuted antecedents. $)
    syl5com $p |- ( ph -> ( ch -> th ) ) $=
      ( a1d sylcom ) ACBDABCEGFH $.
      $( [24-May-2005] $)
  $}

  ${
    $( Premise for ~ com12 .  See ~ pm2.04 for the theorem form. $)
    com12.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Inference that swaps (commutes) antecedents in an implication.  (The
       proof was shortened by Wolf Lammen, 4-Aug-2012.) $)
    com12 $p |- ( ps -> ( ph -> ch ) ) $=
      ( id syl5com ) BBACBEDF $.
      $( [4-Aug-2012] $) $( [5-Aug-1993] $)
  $}

  ${
    syl5.1 $e |- ( ph -> ps ) $.
    syl5.2 $e |- ( ch -> ( ps -> th ) ) $.
    $( A syllogism rule of inference.  The second premise is used to replace
       the second antecedent of the first premise.  (The proof was shortened by
       Wolf Lammen, 25-May-2013.) $)
    syl5 $p |- ( ch -> ( ph -> th ) ) $=
      ( syl5com com12 ) ACDABCDEFGH $.
      $( [25-May-2013] $) $( [5-Aug-1993] $)
  $}

  ${
    syl6.1 $e |- ( ph -> ( ps -> ch ) ) $.
    syl6.2 $e |- ( ch -> th ) $.
    $( A syllogism rule of inference.  The second premise is used to replace
       the consequent of the first premise.  (The proof was shortened by Wolf
       Lammen, 30-Jul-2012.) $)
    syl6 $p |- ( ph -> ( ps -> th ) ) $=
      ( wi a1i sylcom ) ABCDECDGBFHI $.
      $( [31-Jul-2012] $) $( [5-Aug-1993] $)
  $}

  ${
    syl56.1 $e |- ( ph -> ps ) $.
    syl56.2 $e |- ( ch -> ( ps -> th ) ) $.
    syl56.3 $e |- ( th -> ta ) $.
    $( Combine ~ syl5 and ~ syl6 . $)
    syl56 $p |- ( ch -> ( ph -> ta ) ) $=
      ( syl6 syl5 ) ABCEFCBDEGHIJ $.
      $( [14-Nov-2013] $)
  $}

  ${
    syl6com.1 $e |- ( ph -> ( ps -> ch ) ) $.
    syl6com.2 $e |- ( ch -> th ) $.
    $( Syllogism inference with commuted antecedents. $)
    syl6com $p |- ( ps -> ( ph -> th ) ) $=
      ( syl6 com12 ) ABDABCDEFGH $.
      $( [25-May-2005] $)
  $}

  ${
    mpcom.1 $e |- ( ps -> ph ) $.
    mpcom.2 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Modus ponens inference with commutation of antecedents. $)
    mpcom $p |- ( ps -> ch ) $=
      ( com12 mpd ) BACDABCEFG $.
      $( [17-Mar-1996] $)
  $}

  ${
    syli.1 $e |- ( ps -> ( ph -> ch ) ) $.
    syli.2 $e |- ( ch -> ( ph -> th ) ) $.
    $( Syllogism inference with common nested antecedent. $)
    syli $p |- ( ps -> ( ph -> th ) ) $=
      ( com12 sylcom ) BACDECADFGH $.
      $( [4-Nov-2004] $)
  $}

  ${
    syl2im.1 $e |- ( ph -> ps ) $.
    syl2im.2 $e |- ( ch -> th ) $.
    syl2im.3 $e |- ( ps -> ( th -> ta ) ) $.
    $( Replace two antecedents.  Implication-only version of ~ syl2an .
       (Contributed by Wolf Lammen, 14-May-2013.) $)
    syl2im $p |- ( ph -> ( ch -> ta ) ) $=
      ( wi syl5 syl ) ABCEIFCDBEGHJK $.
      $( [14-May-2013] $)
  $}

  $( This theorem, called "Assertion," can be thought of as closed form of
     modus ponens ~ ax-mp .  Theorem *2.27 of [WhiteheadRussell] p. 104. $)
  pm2.27 $p |- ( ph -> ( ( ph -> ps ) -> ps ) ) $=
    ( wi id com12 ) ABCZABFDE $.
    $( [5-Aug-1993] $)

  ${
    mpdd.1 $e |- ( ph -> ( ps -> ch ) ) $.
    mpdd.2 $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
    $( A nested modus ponens deduction. $)
    mpdd $p |- ( ph -> ( ps -> th ) ) $=
      ( wi a2d mpd ) ABCGBDGEABCDFHI $.
      $( [12-Dec-2004] $)
  $}

  ${
    mpid.1 $e |- ( ph -> ch ) $.
    mpid.2 $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
    $( A nested modus ponens deduction. $)
    mpid $p |- ( ph -> ( ps -> th ) ) $=
      ( a1d mpdd ) ABCDACBEGFH $.
      $( [14-Dec-2004] $)
  $}

  ${
    mpdi.1 $e |- ( ps -> ch ) $.
    mpdi.2 $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
    $( A nested modus ponens deduction.  (The proof was shortened by O'Cat,
       15-Jan-2008.) $)
    mpdi $p |- ( ph -> ( ps -> th ) ) $=
      ( wi a1i mpdd ) ABCDBCGAEHFI $.
      $( [15-Jan-2008] $) $( [16-Apr-2005] $)
  $}

  ${
    mpii.1 $e |- ch $.
    mpii.2 $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
    $( A doubly nested modus ponens inference.  (The proof was shortened by
       Wolf Lammen, 31-Jul-2012.) $)
    mpii $p |- ( ph -> ( ps -> th ) ) $=
      ( a1i mpdi ) ABCDCBEGFH $.
      $( [31-Jul-2012] $) $( [31-Dec-1993] $)
  $}

  ${
    syld.1 $e |- ( ph -> ( ps -> ch ) ) $.
    syld.2 $e |- ( ph -> ( ch -> th ) ) $.
    $( Syllogism deduction.  (The proof was shortened by O'Cat, 19-Feb-2008.)
       (The proof was shortened by Wolf Lammen, 3-Aug-2012.)

       Notice that ~ syld has the same form as ~ syl with ` ph ` added in front
       of each hypothesis and conclusion.  When all theorems referenced in a
       proof are converted in this way, we can replace ` ph ` with a hypothesis
       of the proof, allowing the hypothesis to be eliminated with ~ id and
       become an antecedent.  The Deduction Theorem for propositional calculus,
       e.g.  Theorem 3 in [Margaris] p. 56, tells us that this procedure is
       always possible. $)
    syld $p |- ( ph -> ( ps -> th ) ) $=
      ( wi a1d mpdd ) ABCDEACDGBFHI $.
      $( [3-Aug-2012] $) $( [5-Aug-1993] $)
  $}

  ${
    mp2d.1 $e |- ( ph -> ps ) $.
    mp2d.2 $e |- ( ph -> ch ) $.
    mp2d.3 $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
    $( A double modus ponens deduction.  (The proof was shortened by Wolf
       Lammen, 23-Jul-2013.) $)
    mp2d $p |- ( ph -> th ) $=
      ( mpid mpd ) ABDEABCDFGHI $.
      $( [23-Jul-2013] $) $( [23-May-2013] $)
  $}

  ${
    a1dd.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Deduction introducing a nested embedded antecedent.  (The proof was
       shortened by O'Cat, 15-Jan-2008.) $)
    a1dd $p |- ( ph -> ( ps -> ( th -> ch ) ) ) $=
      ( wi ax-1 syl6 ) ABCDCFECDGH $.
      $( [15-Jan-2008] $) $( [17-Dec-2004] $)
  $}

  ${
    pm2.43i.1 $e |- ( ph -> ( ph -> ps ) ) $.
    $( Inference absorbing redundant antecedent.  (The proof was shortened by
       O'Cat, 28-Nov-2008.) $)
    pm2.43i $p |- ( ph -> ps ) $=
      ( id mpd ) AABADCE $.
      $( [29-Nov-2008] $) $( [5-Aug-1993] $)
  $}

  ${
    pm2.43d.1 $e |- ( ph -> ( ps -> ( ps -> ch ) ) ) $.
    $( Deduction absorbing redundant antecedent.  (The proof was shortened by
       O'Cat, 28-Nov-2008.) $)
    pm2.43d $p |- ( ph -> ( ps -> ch ) ) $=
      ( id mpdi ) ABBCBEDF $.
      $( [29-Nov-2008] $) $( [18-Aug-1993] $)
  $}

  ${
    pm2.43a.1 $e |- ( ps -> ( ph -> ( ps -> ch ) ) ) $.
    $( Inference absorbing redundant antecedent.  (The proof was shortened by
       O'Cat, 28-Nov-2008.) $)
    pm2.43a $p |- ( ps -> ( ph -> ch ) ) $=
      ( id mpid ) BABCBEDF $.
      $( [29-Nov-2008] $) $( [7-Nov-1995] $)
  $}

  ${
    pm2.43b.1 $e |- ( ps -> ( ph -> ( ps -> ch ) ) ) $.
    $( Inference absorbing redundant antecedent. $)
    pm2.43b $p |- ( ph -> ( ps -> ch ) ) $=
      ( pm2.43a com12 ) BACABCDEF $.
      $( [31-Oct-1995] $)
  $}

  $( Absorption of redundant antecedent.  Also called the "Contraction" or
     "Hilbert" axiom.  Theorem *2.43 of [WhiteheadRussell] p. 106.  (The proof
     was shortened by O'Cat, 15-Aug-2004.) $)
  pm2.43 $p |- ( ( ph -> ( ph -> ps ) ) -> ( ph -> ps ) ) $=
    ( wi pm2.27 a2i ) AABCBABDE $.
    $( [15-Aug-2004] $) $( [5-Aug-1993] $)

  ${
    imim2d.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Deduction adding nested antecedents. $)
    imim2d $p |- ( ph -> ( ( th -> ps ) -> ( th -> ch ) ) ) $=
      ( wi a1d a2d ) ADBCABCFDEGH $.
      $( [5-Aug-1993] $)
  $}

  $( A closed form of syllogism (see ~ syl ).  Theorem *2.05 of
     [WhiteheadRussell] p. 100.  (The proof was shortened by Wolf Lammen,
     6-Sep-2012.) $)
  imim2 $p |- ( ( ph -> ps ) -> ( ( ch -> ph ) -> ( ch -> ps ) ) ) $=
    ( wi id imim2d ) ABDZABCGEF $.
    $( [6-Sep-2012] $) $( [5-Aug-1993] $)

  ${
    embantd.1 $e |- ( ph -> ps ) $.
    embantd.2 $e |- ( ph -> ( ch -> th ) ) $.
    $( Deduction embedding an antecedent.  (Contributed by Wolf Lammen,
       4-Oct-2013.) $)
    embantd $p |- ( ph -> ( ( ps -> ch ) -> th ) ) $=
      ( wi imim2d mpid ) ABCGBDEACDBFHI $.
      $( [15-Jan-2014] $) $( [4-Oct-2013] $)
  $}

  ${
    3syld.1 $e |- ( ph -> ( ps -> ch ) ) $.
    3syld.2 $e |- ( ph -> ( ch -> th ) ) $.
    3syld.3 $e |- ( ph -> ( th -> ta ) ) $.
    $( Triple syllogism deduction.  (Contributed by Jeff Hankins,
       4-Aug-2009.) $)
    3syld $p |- ( ph -> ( ps -> ta ) ) $=
      ( syld ) ABDEABCDFGIHI $.
      $( [24-Sep-2010] $) $( [4-Aug-2009] $)
  $}

  ${
    sylsyld.1 $e |- ( ph -> ps ) $.
    sylsyld.2 $e |- ( ph -> ( ch -> th ) ) $.
    sylsyld.3 $e |- ( ps -> ( th -> ta ) ) $.
    $( Virtual deduction rule ~ e12 without virtual deduction symbols.
       (Contributed by Alan Sare, 20-Apr-2011.) $)
    sylsyld $p |- ( ph -> ( ch -> ta ) ) $=
      ( wi syl syld ) ACDEGABDEIFHJK $.
      $( [20-Apr-2011] $)
  $}

  ${
    imim12i.1 $e |- ( ph -> ps ) $.
    imim12i.2 $e |- ( ch -> th ) $.
    $( Inference joining two implications.  (The proof was shortened by O'Cat,
       29-Oct-2011.) $)
    imim12i $p |- ( ( ps -> ch ) -> ( ph -> th ) ) $=
      ( wi imim2i syl5 ) ABBCGDECDBFHI $.
      $( [29-Oct-2011] $) $( [5-Aug-1993] $)
  $}

  ${
    imim1i.1 $e |- ( ph -> ps ) $.
    $( Inference adding common consequents in an implication, thereby
       interchanging the original antecedent and consequent.  (The proof was
       shortened by Wolf Lammen, 4-Aug-2012.) $)
    imim1i $p |- ( ( ps -> ch ) -> ( ph -> ch ) ) $=
      ( id imim12i ) ABCCDCEF $.
      $( [4-Aug-2012] $) $( [5-Aug-1993] $)
  $}

  ${
    imim3i.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Inference adding three nested antecedents. $)
    imim3i $p |- ( ( th -> ph ) -> ( ( th -> ps ) -> ( th -> ch ) ) ) $=
      ( wi imim2i a2d ) DAFDBCABCFDEGH $.
      $( [19-Dec-2006] $)
  $}

  ${
    sylc.1 $e |- ( ph -> ps ) $.
    sylc.2 $e |- ( ph -> ch ) $.
    sylc.3 $e |- ( ps -> ( ch -> th ) ) $.
    $( A syllogism inference combined with contraction. $)
    sylc $p |- ( ph -> th ) $=
      ( syl2im pm2.43i ) ADABACDEFGHI $.
      $( [13-Jul-2013] $) $( [4-May-1994] $)
  $}

  ${
    syl3c.1 $e |- ( ph -> ps ) $.
    syl3c.2 $e |- ( ph -> ch ) $.
    syl3c.3 $e |- ( ph -> th ) $.
    syl3c.4 $e |- ( ps -> ( ch -> ( th -> ta ) ) ) $.
    $( A syllogism inference combined with contraction. ~ e111 without virtual
       deductions.  (Contributed by Alan Sare, 7-Jul-2011.) $)
    syl3c $p |- ( ph -> ta ) $=
      ( wi sylc mpd ) ADEHABCDEJFGIKL $.
      $( [7-Jul-2011] $)
  $}

  ${
    syl6mpi.1 $e |- ( ph -> ( ps -> ch ) ) $.
    syl6mpi.2 $e |- th $.
    syl6mpi.3 $e |- ( ch -> ( th -> ta ) ) $.
    $( ~ e20 without virtual deductions.  (Contributed by Alan Sare,
       8-Jul-2011.)  (The proof was shortened by Wolf Lammen, 13-Sep-2012.) $)
    syl6mpi $p |- ( ph -> ( ps -> ta ) ) $=
      ( mpi syl6 ) ABCEFCDEGHIJ $.
      $( [13-Sep-2012] $) $( [8-Jul-2011] $)
  $}

  ${
    mpsyl.1 $e |- ph $.
    mpsyl.2 $e |- ( ps -> ch ) $.
    mpsyl.3 $e |- ( ph -> ( ch -> th ) ) $.
    $( Modus ponens combined with a syllogism inference.  (Contributed by Alan
       Sare, 20-Apr-2011.) $)
    mpsyl $p |- ( ps -> th ) $=
      ( a1i sylc ) BACDABEHFGI $.
      $( [20-Apr-2011] $)
  $}

  ${
    syl6c.1 $e |- ( ph -> ( ps -> ch ) ) $.
    syl6c.2 $e |- ( ph -> ( ps -> th ) ) $.
    syl6c.3 $e |- ( ch -> ( th -> ta ) ) $.
    $( Inference combining ~ syl6 with contraction.  (Contributed by Alan Sare,
       2-May-2011.) $)
    syl6c $p |- ( ph -> ( ps -> ta ) ) $=
      ( wi syl6 mpdd ) ABDEGABCDEIFHJK $.
      $( [2-May-2011] $)
  $}

  ${
    syldd.1 $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
    syldd.2 $e |- ( ph -> ( ps -> ( th -> ta ) ) ) $.
    $( Nested syllogism deduction.  (The proof was shortened by Wolf Lammen,
       11-May-2013.) $)
    syldd $p |- ( ph -> ( ps -> ( ch -> ta ) ) ) $=
      ( wi imim2 syl6c ) ABDEHCDHCEHGFDECIJ $.
      $( [11-May-2013] $) $( [12-Dec-2004] $)
  $}

  ${
    syl5d.1 $e |- ( ph -> ( ps -> ch ) ) $.
    syl5d.2 $e |- ( ph -> ( th -> ( ch -> ta ) ) ) $.
    $( A nested syllogism deduction.  (The proof was shortened by Josh
       Purinton, 29-Dec-2000 and shortened further by O'Cat, 2-Feb-2006.) $)
    syl5d $p |- ( ph -> ( th -> ( ps -> ta ) ) ) $=
      ( wi a1d syldd ) ADBCEABCHDFIGJ $.
      $( [3-Feb-2006] $) $( [5-Aug-1993] $)
  $}

  ${
    syl7.1 $e |- ( ph -> ps ) $.
    syl7.2 $e |- ( ch -> ( th -> ( ps -> ta ) ) ) $.
    $( A syllogism rule of inference.  The second premise is used to replace
       the third antecedent of the first premise.  (The proof was shortened by
       Wolf Lammen, 3-Aug-2012.) $)
    syl7 $p |- ( ch -> ( th -> ( ph -> ta ) ) ) $=
      ( wi a1i syl5d ) CABDEABHCFIGJ $.
      $( [3-Aug-2012] $) $( [5-Aug-1993] $)
  $}

  ${
    syl6d.1 $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
    syl6d.2 $e |- ( ph -> ( th -> ta ) ) $.
    $( A nested syllogism deduction.  (The proof was shortened by Josh
       Purinton, 29-Dec-2000 and shortened further by O'Cat, 2-Feb-2006.) $)
    syl6d $p |- ( ph -> ( ps -> ( ch -> ta ) ) ) $=
      ( wi a1d syldd ) ABCDEFADEHBGIJ $.
      $( [3-Feb-2006] $) $( [5-Aug-1993] $)
  $}

  ${
    syl8.1 $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
    syl8.2 $e |- ( th -> ta ) $.
    $( A syllogism rule of inference.  The second premise is used to replace
       the consequent of the first premise.  (The proof was shortened by Wolf
       Lammen, 3-Aug-2012.) $)
    syl8 $p |- ( ph -> ( ps -> ( ch -> ta ) ) ) $=
      ( wi a1i syl6d ) ABCDEFDEHAGIJ $.
      $( [3-Aug-2012] $) $( [1-Aug-1994] $)
  $}

  ${
    syl9.1 $e |- ( ph -> ( ps -> ch ) ) $.
    syl9.2 $e |- ( th -> ( ch -> ta ) ) $.
    $( A nested syllogism inference with different antecedents.  (The proof was
       shortened by Josh Purinton, 29-Dec-2000.) $)
    syl9 $p |- ( ph -> ( th -> ( ps -> ta ) ) ) $=
      ( wi a1i syl5d ) ABCDEFDCEHHAGIJ $.
      $( [5-Aug-1993] $)
  $}

  ${
    syl9r.1 $e |- ( ph -> ( ps -> ch ) ) $.
    syl9r.2 $e |- ( th -> ( ch -> ta ) ) $.
    $( A nested syllogism inference with different antecedents. $)
    syl9r $p |- ( th -> ( ph -> ( ps -> ta ) ) ) $=
      ( wi syl9 com12 ) ADBEHABCDEFGIJ $.
      $( [5-Aug-1993] $)
  $}

  ${
    imim12d.1 $e |- ( ph -> ( ps -> ch ) ) $.
    imim12d.2 $e |- ( ph -> ( th -> ta ) ) $.
    $( Deduction combining antecedents and consequents.  (The proof was
       shortened by O'Cat, 30-Oct-2011.) $)
    imim12d $p |- ( ph -> ( ( ch -> th ) -> ( ps -> ta ) ) ) $=
      ( wi imim2d syl5d ) ABCCDHEFADECGIJ $.
      $( [3-Nov-2011] $) $( [7-Aug-1994] $)
  $}

  ${
    imim1d.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Deduction adding nested consequents.  (The proof was shortened by Wolf
       Lammen, 12-Sep-2012.) $)
    imim1d $p |- ( ph -> ( ( ch -> th ) -> ( ps -> th ) ) ) $=
      ( idd imim12d ) ABCDDEADFG $.
      $( [12-Sep-2012] $) $( [3-Apr-1994] $)
  $}

  $( A closed form of syllogism (see ~ syl ).  Theorem *2.06 of
     [WhiteheadRussell] p. 100.  (The proof was shortened by Wolf Lammen,
     25-May-2013.) $)
  imim1 $p |- ( ( ph -> ps ) -> ( ( ps -> ch ) -> ( ph -> ch ) ) ) $=
    ( wi id imim1d ) ABDZABCGEF $.
    $( [25-May-2013] $) $( [5-Aug-1993] $)

  $( Theorem *2.83 of [WhiteheadRussell] p. 108. $)
  pm2.83 $p |- ( ( ph -> ( ps -> ch ) ) -> ( ( ph -> ( ch -> th ) ) ->
                ( ph -> ( ps -> th ) ) ) ) $=
    ( wi imim1 imim3i ) BCECDEBDEABCDFG $.
    $( [3-Jan-2005] $)

  ${
    com3.1 $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
    $( Commutation of antecedents.  Swap 2nd and 3rd.  (The proof was shortened
       by Wolf Lammen, 4-Aug-2012.) $)
    com23 $p |- ( ph -> ( ch -> ( ps -> th ) ) ) $=
      ( wi pm2.27 syl9 ) ABCDFCDECDGH $.
      $( [4-Aug-2012] $) $( [5-Aug-1993] $)

    $( Commutation of antecedents.  Rotate right. $)
    com3r $p |- ( ch -> ( ph -> ( ps -> th ) ) ) $=
      ( wi com23 com12 ) ACBDFABCDEGH $.
      $( [25-Apr-1994] $)

    $( Commutation of antecedents.  Swap 1st and 3rd.  (The proof was shortened
       by Wolf Lammen, 28-Jul-2012.) $)
    com13 $p |- ( ch -> ( ps -> ( ph -> th ) ) ) $=
      ( com3r com23 ) CABDABCDEFG $.
      $( [28-Jul-2012] $) $( [25-Apr-1994] $)

    $( Commutation of antecedents.  Rotate left.  (The proof was shortened by
       Wolf Lammen, 28-Jul-2012.) $)
    com3l $p |- ( ps -> ( ch -> ( ph -> th ) ) ) $=
      ( com3r ) CABDABCDEFF $.
      $( [28-Jul-2012] $) $( [25-Apr-1994] $)
  $}

  $( Swap antecedents.  Theorem *2.04 of [WhiteheadRussell] p. 100.  (The proof
     was shortened by Wolf Lammen, 12-Sep-2012.) $)
  pm2.04 $p |- ( ( ph -> ( ps -> ch ) ) -> ( ps -> ( ph -> ch ) ) ) $=
    ( wi id com23 ) ABCDDZABCGEF $.
    $( [12-Sep-2012] $) $( [5-Aug-1993] $)

  ${
    com4.1 $e |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ) $.
    $( Commutation of antecedents.  Swap 3rd and 4th. $)
    com34 $p |- ( ph -> ( ps -> ( th -> ( ch -> ta ) ) ) ) $=
      ( wi pm2.04 syl6 ) ABCDEGGDCEGGFCDEHI $.
      $( [25-Apr-1994] $)

    $( Commutation of antecedents.  Rotate left.  (The proof was shortened by
       O'Cat, 15-Aug-2004.) $)
    com4l $p |- ( ps -> ( ch -> ( th -> ( ph -> ta ) ) ) ) $=
      ( wi com3l com34 ) BCADEABCDEGFHI $.
      $( [15-Aug-2004] $) $( [25-Apr-1994] $)

    $( Commutation of antecedents.  Rotate twice. $)
    com4t $p |- ( ch -> ( th -> ( ph -> ( ps -> ta ) ) ) ) $=
      ( com4l ) BCDAEABCDEFGG $.
      $( [25-Apr-1994] $)

    $( Commutation of antecedents.  Rotate right. $)
    com4r $p |- ( th -> ( ph -> ( ps -> ( ch -> ta ) ) ) ) $=
      ( com4t com4l ) CDABEABCDEFGH $.
      $( [25-Apr-1994] $)

    $( Commutation of antecedents.  Swap 2nd and 4th.  (The proof was shortened
       by Wolf Lammen, 28-Jul-2012.) $)
    com24 $p |- ( ph -> ( th -> ( ch -> ( ps -> ta ) ) ) ) $=
      ( wi com4t com13 ) CDABEGABCDEFHI $.
      $( [28-Jul-2012] $) $( [25-Apr-1994] $)

    $( Commutation of antecedents.  Swap 1st and 4th.  (The proof was shortened
       by Wolf Lammen, 28-Jul-2012.) $)
    com14 $p |- ( th -> ( ps -> ( ch -> ( ph -> ta ) ) ) ) $=
      ( wi com4l com3r ) BCDAEGABCDEFHI $.
      $( [28-Jul-2012] $) $( [25-Apr-1994] $)
  $}

  ${
    com5.1 $e |- ( ph -> ( ps -> ( ch -> ( th -> ( ta -> et ) ) ) ) ) $.
    $( Commutation of antecedents.  Swap 4th and 5th.  (Contributed by Jeff
       Hankins, 28-Jun-2009.) $)
    com45 $p |- ( ph -> ( ps -> ( ch -> ( ta -> ( th -> et ) ) ) ) ) $=
      ( wi pm2.04 syl8 ) ABCDEFHHEDFHHGDEFIJ $.
      $( [18-Apr-2010] $) $( [28-Jun-2009] $)

    $( Commutation of antecedents.  Swap 3rd and 5th.  (Contributed by Jeff
       Hankins, 28-Jun-2009.) $)
    com35 $p |- ( ph -> ( ps -> ( ta -> ( th -> ( ch -> et ) ) ) ) ) $=
      ( wi com34 com45 ) ABDECFHABDCEFABCDEFHGIJI $.
      $( [18-Apr-2010] $) $( [28-Jun-2009] $)

    $( Commutation of antecedents.  Swap 2nd and 5th.  (Contributed by Jeff
       Hankins, 28-Jun-2009.) $)
    com25 $p |- ( ph -> ( ta -> ( ch -> ( th -> ( ps -> et ) ) ) ) ) $=
      ( wi com24 com45 ) ADCEBFHADCBEFABCDEFHGIJI $.
      $( [18-Apr-2010] $) $( [28-Jun-2009] $)

    $( Commutation of antecedents.  Rotate left.  (Contributed by Jeff Hankins,
       28-Jun-2009.)  (The proof was shortened by Wolf Lammen, 29-Jul-2012.) $)
    com5l $p |- ( ps -> ( ch -> ( th -> ( ta -> ( ph -> et ) ) ) ) ) $=
      ( wi com4l com45 ) BCDAEFABCDEFHGIJ $.
      $( [29-Jul-2012] $) $( [28-Jun-2009] $)

    $( Commutation of antecedents.  Swap 1st and 5th.  (Contributed by Jeff
       Hankins, 28-Jun-2009.)  (The proof was shortened by Wolf Lammen,
       29-Jul-2012.) $)
    com15 $p |- ( ta -> ( ps -> ( ch -> ( th -> ( ph -> et ) ) ) ) ) $=
      ( wi com5l com4r ) BCDEAFHABCDEFGIJ $.
      $( [29-Jul-2012] $) $( [28-Jun-2009] $)

    $( Commutation of antecedents.  Rotate left twice.  (Contributed by Jeff
       Hankins, 28-Jun-2009.) $)
    com52l $p |- ( ch -> ( th -> ( ta -> ( ph -> ( ps -> et ) ) ) ) ) $=
      ( com5l ) BCDEAFABCDEFGHH $.
      $( [18-Apr-2010] $) $( [28-Jun-2009] $)

    $( Commutation of antecedents.  Rotate right twice.  (Contributed by Jeff
       Hankins, 28-Jun-2009.) $)
    com52r $p |- ( th -> ( ta -> ( ph -> ( ps -> ( ch -> et ) ) ) ) ) $=
      ( com52l com5l ) CDEABFABCDEFGHI $.
      $( [18-Apr-2010] $) $( [28-Jun-2009] $)

    $( Commutation of antecedents.  Rotate right.  (Contributed by Wolf Lammen,
       29-Jul-2012.) $)
    com5r $p |- ( ta -> ( ph -> ( ps -> ( ch -> ( th -> et ) ) ) ) ) $=
      ( com52l ) CDEABFABCDEFGHH $.
      $( [29-Jul-2012] $)
  $}

  $( Elimination of a nested antecedent as a kind of reversal of inference
     ~ ja .  (Contributed by Wolf Lammen, 9-May-2013.) $)
  jarr $p |- ( ( ( ph -> ps ) -> ch ) -> ( ps -> ch ) ) $=
    ( wi ax-1 imim1i ) BABDCBAEF $.
    $( [9-May-2013] $)

  ${
    pm2.86i.1 $e |- ( ( ph -> ps ) -> ( ph -> ch ) ) $.
    $( Inference based on ~ pm2.86 .  (The proof was shortened by Wolf Lammen,
       3-Apr-2013.) $)
    pm2.86i $p |- ( ph -> ( ps -> ch ) ) $=
      ( wi ax-1 syl com12 ) BACBABEACEBAFDGH $.
      $( [3-Apr-2013] $) $( [5-Aug-1993] $)
  $}

  ${
    pm2.86d.1 $e |- ( ph -> ( ( ps -> ch ) -> ( ps -> th ) ) ) $.
    $( Deduction based on ~ pm2.86 .  (The proof was shortened by Wolf Lammen,
       3-Apr-2013.) $)
    pm2.86d $p |- ( ph -> ( ps -> ( ch -> th ) ) ) $=
      ( wi ax-1 syl5 com23 ) ACBDCBCFABDFCBGEHI $.
      $( [3-Apr-2013] $) $( [29-Jun-1995] $)
  $}

  $( Converse of axiom ~ ax-2 .  Theorem *2.86 of [WhiteheadRussell] p. 108.
     (The proof was shortened by Wolf Lammen, 3-Apr-2013.) $)
  pm2.86 $p |- ( ( ( ph -> ps ) -> ( ph -> ch ) ) ->
              ( ph -> ( ps -> ch ) ) ) $=
    ( wi id pm2.86d ) ABDACDDZABCGEF $.
    $( [3-Apr-2013] $) $( [25-Apr-1994] $)

  $( The Linearity Axiom of the infinite-valued sentential logic (L-infinity)
     of Lukasiewicz.  This version of ~ loolin does not use ~ ax-3 , meaning
     that this theorem is intuitionistically valid.  (Contributed by O'Cat,
     12-Aug-2004.) $)
  loolinALT $p |- ( ( ( ph -> ps ) -> ( ps -> ph ) ) -> ( ps -> ph ) ) $=
    ( wi jarr pm2.43d ) ABCBACZCBAABFDE $.
    $( [21-Sep-2013] $) $( [12-Aug-2004] $)

  $( An alternate for the Linearity Axiom of the infinite-valued sentential
     logic (L-infinity) of Lukasiewicz, due to Barbara Wozniakowska, _Reports
     on Mathematical Logic_ 10, 129-137 (1978).  (Contributed by O'Cat,
     8-Aug-2004.) $)
  loowoz $p |- ( ( ( ph -> ps ) -> ( ph -> ch ) ) ->
                 ( ( ps -> ph ) -> ( ps -> ch ) ) ) $=
    ( wi jarr a2d ) ABDACDZDBACABGEF $.
    $( [20-Sep-2013] $) $( [8-Aug-2004] $)

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Logical negation
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

$( This section makes our first use of the third axiom of propositonal
   calculus. $)

  ${
    con4d.1 $e |- ( ph -> ( -. ps -> -. ch ) ) $.
    $( Deduction derived from axiom ~ ax-3 . $)
    con4d $p |- ( ph -> ( ch -> ps ) ) $=
      ( wn wi ax-3 syl ) ABECEFCBFDBCGH $.
      $( [26-Mar-1995] $)
  $}

  ${
    pm2.21d.1 $e |- ( ph -> -. ps ) $.
    $( A contradiction implies anything.  Deduction from ~ pm2.21 . $)
    pm2.21d $p |- ( ph -> ( ps -> ch ) ) $=
      ( wn a1d con4d ) ACBABECEDFG $.
      $( [10-Feb-1996] $)
  $}

  $( From a wff and its negation, anything is true.  Theorem *2.21 of
     [WhiteheadRussell] p. 104.  Also called the Duns Scotus law.  (The proof
     was shortened by Wolf Lammen, 14-Sep-2012.) $)
  pm2.21 $p |- ( -. ph -> ( ph -> ps ) ) $=
    ( wn id pm2.21d ) ACZABFDE $.
    $( [14-Sep-2012] $) $( [5-Aug-1993] $)

  $( Theorem *2.24 of [WhiteheadRussell] p. 104. $)
  pm2.24 $p |- ( ph -> ( -. ph -> ps ) ) $=
    ( wn pm2.21 com12 ) ACABABDE $.
    $( [3-Jan-2005] $)

  $( Proof by contradiction.  Theorem *2.18 of [WhiteheadRussell] p. 103.  Also
     called the Law of Clavius. $)
  pm2.18 $p |- ( ( -. ph -> ph ) -> ph ) $=
    ( wn wi pm2.21 a2i con4d pm2.43i ) ABZACZAIAIHAIBZAJDEFG $.
    $( [5-Aug-1993] $)

  ${
    pm2.18d.1 $e |- ( ph -> ( -. ps -> ps ) ) $.
    $( Deduction based on reductio ad absurdum.  (Contributed by FL,
       12-Jul-2009.)  (The proof was shortened by Andrew Salmon,
       7-May-2011.) $)
    pm2.18d $p |- ( ph -> ps ) $=
      ( wn wi pm2.18 syl ) ABDBEBCBFG $.
      $( [7-May-2011] $) $( [12-Jul-2009] $)
  $}

  $( Converse of double negation.  Theorem *2.14 of [WhiteheadRussell] p. 102.
     (The proof was shortened by David Harvey, 5-Sep-1999.  An even shorter
     proof found by Josh Purinton, 29-Dec-2000.) $)
  notnot2 $p |- ( -. -. ph -> ph ) $=
    ( wn pm2.21 pm2.18d ) ABZBAEACD $.
    $( [5-Aug-1993] $)

  ${
    negai.1 $e |- -. -. ph $.
    $( Inference from double negation. $)
    notnotri $p |- ph $=
      ( wn notnot2 ax-mp ) ACCABADE $.
      $( [27-Feb-2008] $)
  $}

  ${
    con2d.1 $e |- ( ph -> ( ps -> -. ch ) ) $.
    $( A contraposition deduction. $)
    con2d $p |- ( ph -> ( ch -> -. ps ) ) $=
      ( wn notnot2 syl5 con4d ) ABEZCIEBACEBFDGH $.
      $( [12-Feb-2013] $) $( [19-Aug-1993] $)
  $}

  $( Contraposition.  Theorem *2.03 of [WhiteheadRussell] p. 100.  (The proof
     was shortened by Wolf Lammen, 12-Feb-2013.) $)
  con2 $p |- ( ( ph -> -. ps ) -> ( ps -> -. ph ) ) $=
    ( wn wi id con2d ) ABCDZABGEF $.
    $( [12-Feb-2013] $) $( [5-Aug-1993] $)

  ${
    mt2d.1 $e |- ( ph -> ch ) $.
    mt2d.2 $e |- ( ph -> ( ps -> -. ch ) ) $.
    $( Modus tollens deduction. $)
    mt2d $p |- ( ph -> -. ps ) $=
      ( wn con2d mpd ) ACBFDABCEGH $.
      $( [4-Jul-1994] $)
  $}

  ${
    mt2i.1 $e |- ch $.
    mt2i.2 $e |- ( ph -> ( ps -> -. ch ) ) $.
    $( Modus tollens inference.  (The proof was shortened by Wolf Lammen,
       15-Sep-2012.) $)
    mt2i $p |- ( ph -> -. ps ) $=
      ( a1i mt2d ) ABCCADFEG $.
      $( [15-Sep-2012] $) $( [26-Mar-1995] $)
  $}

  ${
    nsyl3.1 $e |- ( ph -> -. ps ) $.
    nsyl3.2 $e |- ( ch -> ps ) $.
    $( A negated syllogism inference. $)
    nsyl3 $p |- ( ch -> -. ph ) $=
      ( wn wi a1i mt2d ) CABEABFGCDHI $.
      $( [13-Jun-2013] $) $( [1-Dec-1995] $)
  $}

  ${
    con2i.a $e |- ( ph -> -. ps ) $.
    $( A contraposition inference.  (The proof was shortened by O'Cat,
       28-Nov-2008.)  (The proof was shortened by Wolf Lammen, 13-Jun-2013.) $)
    con2i $p |- ( ps -> -. ph ) $=
      ( id nsyl3 ) ABBCBDE $.
      $( [13-Jun-2013] $) $( [5-Aug-1993] $)
  $}

  ${
    nsyl.1 $e |- ( ph -> -. ps ) $.
    nsyl.2 $e |- ( ch -> ps ) $.
    $( A negated syllogism inference.  (The proof was shortened by Wolf Lammen,
       2-Mar-2013.) $)
    nsyl $p |- ( ph -> -. ch ) $=
      ( nsyl3 con2i ) CAABCDEFG $.
      $( [2-Mar-2013] $) $( [31-Dec-1993] $)
  $}

  $( Converse of double negation.  Theorem *2.12 of [WhiteheadRussell] p. 101.
     (The proof was shortened by Wolf Lammen, 2-Mar-2013.) $)
  notnot1 $p |- ( ph -> -. -. ph ) $=
    ( wn id con2i ) ABZAECD $.
    $( [2-Mar-2013] $) $( [5-Aug-1993] $)

  ${
    negbi.1 $e |- ph $.
    $( Infer double negation. $)
    notnoti $p |- -. -. ph $=
      ( wn notnot1 ax-mp ) AACCBADE $.
      $( [27-Feb-2008] $)
  $}

  ${
    con1d.1 $e |- ( ph -> ( -. ps -> ch ) ) $.
    $( A contraposition deduction. $)
    con1d $p |- ( ph -> ( -. ch -> ps ) ) $=
      ( wn notnot1 syl6 con4d ) ABCEZABECIEDCFGH $.
      $( [12-Feb-2013] $) $( [5-Aug-1993] $)
  $}

  ${
    mt3d.1 $e |- ( ph -> -. ch ) $.
    mt3d.2 $e |- ( ph -> ( -. ps -> ch ) ) $.
    $( Modus tollens deduction. $)
    mt3d $p |- ( ph -> ps ) $=
      ( wn con1d mpd ) ACFBDABCEGH $.
      $( [26-Mar-1995] $)
  $}

  ${
    mt3i.1 $e |- -. ch $.
    mt3i.2 $e |- ( ph -> ( -. ps -> ch ) ) $.
    $( Modus tollens inference.  (The proof was shortened by Wolf Lammen,
       15-Sep-2012.) $)
    mt3i $p |- ( ph -> ps ) $=
      ( wn a1i mt3d ) ABCCFADGEH $.
      $( [15-Sep-2012] $) $( [26-Mar-1995] $)
  $}

  ${
    nsyl2.1 $e |- ( ph -> -. ps ) $.
    nsyl2.2 $e |- ( -. ch -> ps ) $.
    $( A negated syllogism inference. $)
    nsyl2 $p |- ( ph -> ch ) $=
      ( wn wi a1i mt3d ) ACBDCFBGAEHI $.
      $( [19-Jun-2013] $) $( [26-Jun-1994] $)
  $}

  $( Contraposition.  Theorem *2.15 of [WhiteheadRussell] p. 102.  (The proof
     was shortened by Wolf Lammen, 12-Feb-2013.) $)
  con1 $p |- ( ( -. ph -> ps ) -> ( -. ps -> ph ) ) $=
    ( wn wi id con1d ) ACBDZABGEF $.
    $( [12-Feb-2013] $) $( [5-Aug-1993] $)

  ${
    con1i.a $e |- ( -. ph -> ps ) $.
    $( A contraposition inference.  (The proof was shortened by O'Cat,
       28-Nov-2008.)  (The proof was shortened by Wolf Lammen, 19-Jun-2013.) $)
    con1i $p |- ( -. ps -> ph ) $=
      ( wn id nsyl2 ) BDZBAGECF $.
      $( [19-Jun-2013] $) $( [5-Aug-1993] $)
  $}

  ${
    con4i.1 $e |- ( -. ph -> -. ps ) $.
    $( Inference rule derived from axiom ~ ax-3 .  (The proof was shortened by
       Wolf Lammen, 21-Jun-2013.) $)
    con4i $p |- ( ps -> ph ) $=
      ( wn notnot1 nsyl2 ) BBDABECF $.
      $( [21-Jun-2013] $) $( [5-Aug-1993] $)
  $}

  ${
    pm2.21i.1 $e |- -. ph $.
    $( A contradiction implies anything.  Inference from ~ pm2.21 . $)
    pm2.21i $p |- ( ph -> ps ) $=
      ( wn a1i con4i ) BAADBDCEF $.
      $( [16-Sep-1993] $)
  $}

  ${
    pm2.24ii.1 $e |- ph $.
    pm2.24ii.2 $e |- -. ph $.
    $( A contradiction implies anything.  Inference from ~ pm2.24 . $)
    pm2.24ii $p |- ps $=
      ( pm2.21i ax-mp ) ABCABDEF $.
      $( [27-Feb-2008] $)
  $}

  ${
    con3d.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( A contraposition deduction. $)
    con3d $p |- ( ph -> ( -. ch -> -. ps ) ) $=
      ( wn notnot2 syl5 con1d ) ABEZCIEBACBFDGH $.
      $( [13-Feb-2013] $) $( [5-Aug-1993] $)
  $}

  $( Contraposition.  Theorem *2.16 of [WhiteheadRussell] p. 103.  (The proof
     was shortened by Wolf Lammen, 13-Feb-2013.) $)
  con3 $p |- ( ( ph -> ps ) -> ( -. ps -> -. ph ) ) $=
    ( wi id con3d ) ABCZABFDE $.
    $( [13-Feb-2013] $) $( [5-Aug-1993] $)

  ${
    con3i.a $e |- ( ph -> ps ) $.
    $( A contraposition inference.  (The proof was shortened by Wolf Lammen,
       20-Jun-2013.) $)
    con3i $p |- ( -. ps -> -. ph ) $=
      ( wn id nsyl ) BDZBAGECF $.
      $( [20-Jun-2013] $) $( [5-Aug-1993] $)
  $}

  ${
    con3rr3.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Rotate through consequent right.  (Contributed by Wolf Lammen,
       3-Nov-2013.) $)
    con3rr3 $p |- ( -. ch -> ( ph -> -. ps ) ) $=
      ( wn con3d com12 ) ACEBEABCDFG $.
      $( [3-Nov-2013] $)
  $}

  ${
    mt4.1 $e |- ph $.
    mt4.2 $e |- ( -. ps -> -. ph ) $.
    $( The rule of modus tollens.  (Contributed by Wolf Lammen,
       12-May-2013.) $)
    mt4 $p |- ps $=
      ( con4i ax-mp ) ABCBADEF $.
      $( [12-May-2013] $)
  $}

  ${
    mt4d.1 $e |- ( ph -> ps ) $.
    mt4d.2 $e |- ( ph -> ( -. ch -> -. ps ) ) $.
    $( Modus tollens deduction. $)
    mt4d $p |- ( ph -> ch ) $=
      ( con4d mpd ) ABCDACBEFG $.
      $( [9-Jun-2006] $)
  $}

  ${
    mt4i.1 $e |- ch $.
    mt4i.2 $e |- ( ph -> ( -. ps -> -. ch ) ) $.
    $( Modus tollens inference.  (Contributed by Wolf Lammen, 12-May-2013.) $)
    mt4i $p |- ( ph -> ps ) $=
      ( a1i mt4d ) ACBCADFEG $.
      $( [10-Sep-2013] $) $( [12-May-2013] $)
  $}

  ${
    nsyld.1 $e |- ( ph -> ( ps -> -. ch ) ) $.
    nsyld.2 $e |- ( ph -> ( ta -> ch ) ) $.
    $( A negated syllogism deduction. $)
    nsyld $p |- ( ph -> ( ps -> -. ta ) ) $=
      ( wn con3d syld ) ABCGDGEADCFHI $.
      $( [9-Apr-2005] $)
  $}

  ${
    nsyli.1 $e |- ( ph -> ( ps -> ch ) ) $.
    nsyli.2 $e |- ( th -> -. ch ) $.
    $( A negated syllogism inference. $)
    nsyli $p |- ( ph -> ( th -> -. ps ) ) $=
      ( wn con3d syl5 ) DCGABGFABCEHI $.
      $( [3-May-1994] $)
  $}

  ${
    nsyl4.1 $e |- ( ph -> ps ) $.
    nsyl4.2 $e |- ( -. ph -> ch ) $.
    $( A negated syllogism inference. $)
    nsyl4 $p |- ( -. ch -> ps ) $=
      ( wn con1i syl ) CFABACEGDH $.
      $( [15-Feb-1996] $)
  $}

  ${
    pm2.24d.1 $e |- ( ph -> ps ) $.
    $( Deduction version of ~ pm2.24 . $)
    pm2.24d $p |- ( ph -> ( -. ps -> ch ) ) $=
      ( wn a1d con1d ) ACBABCEDFG $.
      $( [30-Jan-2006] $)
  $}

  ${
    pm2.24i.1 $e |- ph $.
    $( Inference version of ~ pm2.24 . $)
    pm2.24i $p |- ( -. ph -> ps ) $=
      ( wn a1i con1i ) BAABDCEF $.
      $( [20-Aug-2001] $)
  $}

  $( Theorem *3.2 of [WhiteheadRussell] p. 111, expressed with primitive
     connectives.  (The proof was shortened by Josh Purinton, 29-Dec-2000.) $)
  pm3.2im $p |- ( ph -> ( ps -> -. ( ph -> -. ps ) ) ) $=
    ( wn wi pm2.27 con2d ) AABCZDBAGEF $.
    $( [5-Aug-1993] $)

  $( Theorem 8 of [Margaris] p. 60.  (The proof was shortened by Josh Purinton,
     29-Dec-2000.) $)
  mth8 $p |- ( ph -> ( -. ps -> -. ( ph -> ps ) ) ) $=
    ( wi pm2.27 con3d ) AABCBABDE $.
    $( [5-Aug-1993] $)

  ${
    jc.1 $e |- ( ph -> ps ) $.
    jc.2 $e |- ( ph -> ch ) $.
    $( Inference joining the consequents of two premises. $)
    jc $p |- ( ph -> -. ( ps -> -. ch ) ) $=
      ( wn wi pm3.2im sylc ) ABCBCFGFDEBCHI $.
      $( [5-Aug-1993] $)
  $}

  ${
    impi.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( An importation inference.  (The proof was shortened by Wolf Lammen,
       20-Jul-2013.) $)
    impi $p |- ( -. ( ph -> -. ps ) -> ch ) $=
      ( wn wi con3rr3 con1i ) CABEFABCDGH $.
      $( [20-Jul-2013] $) $( [5-Aug-1993] $)
  $}

  ${
    expi.1 $e |- ( -. ( ph -> -. ps ) -> ch ) $.
    $( An exportation inference.  (The proof was shortened by O'Cat,
       28-Nov-2008.) $)
    expi $p |- ( ph -> ( ps -> ch ) ) $=
      ( wn wi pm3.2im syl6 ) ABABEFECABGDH $.
      $( [29-Nov-2008] $) $( [5-Aug-1993] $)
  $}

  $( Simplification.  Similar to Theorem *3.27 (Simp) of [WhiteheadRussell]
     p. 112.  (The proof was shortened by Wolf Lammen, 13-Nov-2012.) $)
  simprim $p |- ( -. ( ph -> -. ps ) -> ps ) $=
    ( idd impi ) ABBABCD $.
    $( [13-Nov-2012] $) $( [5-Aug-1993] $)

  $( Simplification.  Similar to Theorem *3.26 (Simp) of [WhiteheadRussell]
     p. 112.  (The proof was shortened by Wolf Lammen, 21-Jul-2012.) $)
  simplim $p |- ( -. ( ph -> ps ) -> ph ) $=
    ( wi pm2.21 con1i ) AABCABDE $.
    $( [23-Jul-2012] $) $( [5-Aug-1993] $)

  $( Theorem *2.5 of [WhiteheadRussell] p. 107.  (The proof was shortened by
     Wolf Lammen, 9-Oct-2012.) $)
  pm2.5 $p |- ( -. ( ph -> ps ) -> ( -. ph -> ps ) ) $=
    ( wi wn simplim pm2.24d ) ABCDABABEF $.
    $( [9-Oct-2012] $) $( [3-Jan-2005] $)

  $( Theorem *2.51 of [WhiteheadRussell] p. 107. $)
  pm2.51 $p |- ( -. ( ph -> ps ) -> ( ph -> -. ps ) ) $=
    ( wi wn ax-1 con3i a1d ) ABCZDBDABHBAEFG $.
    $( [3-Jan-2005] $)

  $( Theorem *2.521 of [WhiteheadRussell] p. 107.  (The proof was shortened by
     Wolf Lammen, 8-Oct-2012.) $)
  pm2.521 $p |- ( -. ( ph -> ps ) -> ( ps -> ph ) ) $=
    ( wi wn simplim a1d ) ABCDABABEF $.
    $( [8-Oct-2012] $) $( [3-Jan-2005] $)

  $( Theorem *2.52 of [WhiteheadRussell] p. 107.  (The proof was shortened by
     Wolf Lammen, 8-Oct-2012.) $)
  pm2.52 $p |- ( -. ( ph -> ps ) -> ( -. ph -> -. ps ) ) $=
    ( wi wn pm2.521 con3d ) ABCDBAABEF $.
    $( [8-Oct-2012] $) $( [3-Jan-2005] $)

  $( Exportation theorem expressed with primitive connectives. $)
  expt $p |- ( ( -. ( ph -> -. ps ) -> ch ) -> ( ph -> ( ps -> ch ) ) ) $=
    ( wn wi pm3.2im imim1d com12 ) AABDEDZCEBCEABICABFGH $.
    $( [5-Aug-1993] $)

  $( Importation theorem expressed with primitive connectives.  (The proof was
     shortened by Wolf Lammen, 20-Jul-2013.) $)
  impt $p |- ( ( ph -> ( ps -> ch ) ) -> ( -. ( ph -> -. ps ) -> ch ) ) $=
    ( wi wn simprim simplim imim1i mpdi ) ABCDZDABEZDEZBCABFLAJAKGHI $.
    $( [20-Jul-2013] $) $( [25-Apr-1994] $)

  ${
    pm2.61d.1 $e |- ( ph -> ( ps -> ch ) ) $.
    pm2.61d.2 $e |- ( ph -> ( -. ps -> ch ) ) $.
    $( Deduction eliminating an antecedent.  (The proof was shortened by Wolf
       Lammen, 12-Sep-2013.) $)
    pm2.61d $p |- ( ph -> ch ) $=
      ( wn con1d syld pm2.18d ) ACACFBCABCEGDHI $.
      $( [12-Sep-2013] $) $( [27-Apr-1994] $)
  $}

  ${
    pm2.61d1.1 $e |- ( ph -> ( ps -> ch ) ) $.
    pm2.61d1.2 $e |- ( -. ps -> ch ) $.
    $( Inference eliminating an antecedent. $)
    pm2.61d1 $p |- ( ph -> ch ) $=
      ( wn wi a1i pm2.61d ) ABCDBFCGAEHI $.
      $( [15-Jul-2005] $)
  $}

  ${
    pm2.61d2.1 $e |- ( ph -> ( -. ps -> ch ) ) $.
    pm2.61d2.2 $e |- ( ps -> ch ) $.
    $( Inference eliminating an antecedent. $)
    pm2.61d2 $p |- ( ph -> ch ) $=
      ( wi a1i pm2.61d ) ABCBCFAEGDH $.
      $( [18-Aug-1993] $)
  $}

  ${
    ja.1 $e |- ( -. ph -> ch ) $.
    ja.2 $e |- ( ps -> ch ) $.
    $( Inference joining the antecedents of two premises.  (The proof was
       shortened by O'Cat, 19-Feb-2008.) $)
    ja $p |- ( ( ph -> ps ) -> ch ) $=
      ( wi imim2i pm2.61d1 ) ABFACBCAEGDH $.
      $( [19-Feb-2008] $) $( [5-Aug-1993] $)
  $}

  ${
    jad.1 $e |- ( ph -> ( -. ps -> th ) ) $.
    jad.2 $e |- ( ph -> ( ch -> th ) ) $.
    $( Deduction form of ~ ja .  (Contributed by Scott Fenton, 13-Dec-2010.)
       (The proof was shortened by Andrew Salmon, 17-Sep-2011.) $)
    jad $p |- ( ph -> ( ( ps -> ch ) -> th ) ) $=
      ( wi wn com12 ja ) BCGADBCADGABHDEIACDFIJI $.
      $( [17-Sep-2011] $) $( [13-Dec-2010] $)
  $}

  $( Elimination of a nested antecedent as a kind of reversal of inference
     ~ ja .  (Contributed by Wolf Lammen, 10-May-2013.) $)
  jarl $p |- ( ( ( ph -> ps ) -> ch ) -> ( -. ph -> ch ) ) $=
    ( wn wi pm2.21 imim1i ) ADABECABFG $.
    $( [10-May-2013] $)

  ${
    pm2.61i.1 $e |- ( ph -> ps ) $.
    pm2.61i.2 $e |- ( -. ph -> ps ) $.
    $( Inference eliminating an antecedent.  (The proof was shortened by Wolf
       Lammen, 12-Sep-2013.) $)
    pm2.61i $p |- ps $=
      ( wi id ja ax-mp ) AAEBAFAABDCGH $.
      $( [12-Sep-2013] $) $( [5-Apr-1994] $)
  $}

  ${
    pm2.61ii.1 $e |- ( -. ph -> ( -. ps -> ch ) ) $.
    pm2.61ii.2 $e |- ( ph -> ch ) $.
    pm2.61ii.3 $e |- ( ps -> ch ) $.
    $( Inference eliminating two antecedents.  (The proof was shortened by Josh
       Purinton, 29-Dec-2000.) $)
    pm2.61ii $p |- ch $=
      ( wn pm2.61d2 pm2.61i ) ACEAGBCDFHI $.
      $( [5-Aug-1993] $)
  $}

  ${
    pm2.61nii.1 $e |- ( ph -> ( ps -> ch ) ) $.
    pm2.61nii.2 $e |- ( -. ph -> ch ) $.
    pm2.61nii.3 $e |- ( -. ps -> ch ) $.
    $( Inference eliminating two antecedents.  (The proof was shortened by
       Andrew Salmon, 25-May-2011.)  (The proof was shortened by Wolf Lammen,
       13-Nov-2012.) $)
    pm2.61nii $p |- ch $=
      ( pm2.61d1 pm2.61i ) ACABCDFGEH $.
      $( [13-Nov-2012] $) $( [5-Aug-1993] $)
  $}

  ${
    pm2.61iii.1 $e |- ( -. ph -> ( -. ps -> ( -. ch -> th ) ) ) $.
    pm2.61iii.2 $e |- ( ph -> th ) $.
    pm2.61iii.3 $e |- ( ps -> th ) $.
    pm2.61iii.4 $e |- ( ch -> th ) $.
    $( Inference eliminating three antecedents.  (The proof was shortened by
       Wolf Lammen, 22-Sep-2013.) $)
    pm2.61iii $p |- th $=
      ( wn wi a1d pm2.61ii pm2.61i ) CDHABCIZDJEADNFKBDNGKLM $.
      $( [22-Sep-2013] $) $( [2-Jan-2002] $)
  $}

  $( Reductio ad absurdum.  Theorem *2.01 of [WhiteheadRussell] p. 100.  (The
     proof was shortened by O'Cat, 21-Nov-2008.)  (The proof was shortened by
     Wolf Lammen, 31-Oct-2012.) $)
  pm2.01 $p |- ( ( ph -> -. ph ) -> -. ph ) $=
    ( wn id ja ) AABZEECZFD $.
    $( [31-Oct-2012] $) $( [18-Aug-1993] $)

  ${
    pm2.01d.1 $e |- ( ph -> ( ps -> -. ps ) ) $.
    $( Deduction based on reductio ad absurdum.  (The proof was shortened by
       Wolf Lammen, 5-Mar-2013.) $)
    pm2.01d $p |- ( ph -> -. ps ) $=
      ( wn id pm2.61d1 ) ABBDZCGEF $.
      $( [5-Mar-2013] $) $( [18-Aug-1993] $)
  $}

  $( Theorem *2.6 of [WhiteheadRussell] p. 107. $)
  pm2.6 $p |- ( ( -. ph -> ps ) -> ( ( ph -> ps ) -> ps ) ) $=
    ( wn wi id idd jad ) ACBDZABBHEHBFG $.
    $( [22-Sep-2013] $) $( [3-Jan-2005] $)

  $( Theorem *2.61 of [WhiteheadRussell] p. 107.  Useful for eliminating an
     antecedent.  (The proof was shortened by Wolf Lammen, 22-Sep-2013.) $)
  pm2.61 $p |- ( ( ph -> ps ) -> ( ( -. ph -> ps ) -> ps ) ) $=
    ( wn wi pm2.6 com12 ) ACBDABDBABEF $.
    $( [22-Sep-2013] $) $( [5-Aug-1993] $)

  $( Theorem *2.65 of [WhiteheadRussell] p. 107.  Proof by contradiction.  (The
     proof was shortened by Wolf Lammen, 8-Mar-2013.) $)
  pm2.65 $p |- ( ( ph -> ps ) -> ( ( ph -> -. ps ) -> -. ph ) ) $=
    ( wi wn idd con3 jad ) ABCZABDADZHIEABFG $.
    $( [8-Mar-2013] $) $( [5-Aug-1993] $)

  ${
    pm2.65i.1 $e |- ( ph -> ps ) $.
    pm2.65i.2 $e |- ( ph -> -. ps ) $.
    $( Inference rule for proof by contradiction.  (The proof was shortened by
       Wolf Lammen, 11-Sep-2013.) $)
    pm2.65i $p |- -. ph $=
      ( wn con2i con3i pm2.61i ) BAEABDFABCGH $.
      $( [11-Sep-2013] $) $( [18-May-1994] $)
  $}

  ${
    pm2.65d.1 $e |- ( ph -> ( ps -> ch ) ) $.
    pm2.65d.2 $e |- ( ph -> ( ps -> -. ch ) ) $.
    $( Deduction rule for proof by contradiction.  (The proof was shortened by
       Wolf Lammen, 26-May-2013.) $)
    pm2.65d $p |- ( ph -> -. ps ) $=
      ( nsyld pm2.01d ) ABABCBEDFG $.
      $( [26-May-2013] $) $( [26-Jun-1994] $)
  $}

  ${
    mto.1 $e |- -. ps $.
    mto.2 $e |- ( ph -> ps ) $.
    $( The rule of modus tollens.  (The proof was shortened by Wolf Lammen,
       11-Sep-2013.) $)
    mto $p |- -. ph $=
      ( wn a1i pm2.65i ) ABDBEACFG $.
      $( [11-Sep-2013] $) $( [19-Aug-1993] $)
  $}

  ${
    mtod.1 $e |- ( ph -> -. ch ) $.
    mtod.2 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Modus tollens deduction.  (The proof was shortened by Wolf Lammen,
       11-Sep-2013.) $)
    mtod $p |- ( ph -> -. ps ) $=
      ( wn a1d pm2.65d ) ABCEACFBDGH $.
      $( [11-Sep-2013] $) $( [3-Apr-1994] $)
  $}

  ${
    mtoi.1 $e |- -. ch $.
    mtoi.2 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Modus tollens inference.  (The proof was shortened by Wolf Lammen,
       15-Sep-2012.) $)
    mtoi $p |- ( ph -> -. ps ) $=
      ( wn a1i mtod ) ABCCFADGEH $.
      $( [15-Sep-2012] $) $( [5-Jul-1994] $)
  $}

  ${
    mt2.1 $e |- ps $.
    mt2.2 $e |- ( ph -> -. ps ) $.
    $( A rule similar to modus tollens.  (The proof was shortened by Wolf
       Lammen, 10-Sep-2013.) $)
    mt2 $p |- -. ph $=
      ( a1i pm2.65i ) ABBACEDF $.
      $( [10-Sep-2013] $) $( [19-Aug-1993] $)
  $}

  ${
    mt3.1 $e |- -. ps $.
    mt3.2 $e |- ( -. ph -> ps ) $.
    $( A rule similar to modus tollens.  (The proof was shortened by Wolf
       Lammen, 11-Sep-2013.) $)
    mt3 $p |- ph $=
      ( wn mto notnotri ) AAEBCDFG $.
      $( [11-Sep-2013] $) $( [18-May-1994] $)
  $}

  $( Peirce's axiom.  This odd-looking theorem is the "difference" between an
     intuitionistic system of propositional calculus and a classical system and
     is not accepted by intuitionists.  When Peirce's axiom is added to an
     intuitionistic system, the system becomes equivalent to our classical
     system ~ ax-1 through ~ ax-3 .  A curious fact about this theorem is that
     it requires ~ ax-3 for its proof even though the result has no negation
     connectives in it.  (The proof was shortened by Wolf Lammen,
     9-Oct-2012.) $)
  peirce $p |- ( ( ( ph -> ps ) -> ph ) -> ph ) $=
    ( wi simplim id ja ) ABCAAABDAEF $.
    $( [9-Oct-2012] $) $( [5-Aug-1993] $)

  $( The Linearity Axiom of the infinite-valued sentential logic (L-infinity)
     of Lukasiewicz.  For a version not using ~ ax-3 , see ~ loolinALT .
     (Contributed by O'Cat, 12-Aug-2004.)  (The proof was shortened by Wolf
     Lammen, 2-Nov-2012.) $)
  loolin $p |- ( ( ( ph -> ps ) -> ( ps -> ph ) ) -> ( ps -> ph ) ) $=
    ( wi pm2.521 id ja ) ABCBACZGABDGEF $.
    $( [2-Nov-2012] $) $( [12-Aug-2004] $)

  $( The Inversion Axiom of the infinite-valued sentential logic (L-infinity)
     of Lukasiewicz.  Using ~ dfor2 , we can see that this essentially
     expresses "disjunction commutes."  Theorem *2.69 of [WhiteheadRussell]
     p. 108. $)
  looinv $p |- ( ( ( ph -> ps ) -> ps ) -> ( ( ps -> ph ) -> ph ) ) $=
    ( wi imim1 peirce syl6 ) ABCZBCBACGACAGBADABEF $.
    $( [12-Aug-2004] $)

  $( Theorem used to justify definition of biconditional ~ df-bi .  (The proof
     was shortened by Josh Purinton, 29-Dec-2000.) $)
  bijust $p |- -. ( ( -. ( ( ph -> ps ) -> -. ( ps -> ph ) )
                      -> -. ( ( ph -> ps ) -> -. ( ps -> ph ) ) )
               -> -. ( -. ( ( ph -> ps ) -> -. ( ps -> ph ) )
                      -> -. ( ( ph -> ps ) -> -. ( ps -> ph ) ) ) ) $=
    ( wi wn id pm2.01 mt2 ) ABCBACDCDZHCZIDCIHEIFG $.
    $( [18-Nov-2013] $) $( [11-May-1999] $)

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Logical equivalence
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Declare the biconditional connective. $)
  $c <-> $. $( Double arrow (read:  'if and only if' or
               'is logically equivalent to') $)

  $( Extend our wff definition to include the biconditional connective. $)
  wb $a wff ( ph <-> ps ) $.

  $( This is our first definition, which introduces and defines the
     biconditional connective ` <-> ` .  We define a wff of the form
     ` ( ph <-> ps ) ` as an abbreviation for
     ` -. ( ( ph -> ps ) -> -. ( ps -> ph ) ) ` .

     Unlike most traditional developments, we have chosen not to have a
     separate symbol such as "Df." to mean "is defined as."  Instead, we will
     later use the biconditional connective for this purpose ( ~ df-or is its
     first use), as it allows us to use logic to manipulate definitions
     directly.  This greatly simplifies many proofs since it eliminates the
     need for a separate mechanism for introducing and eliminating
     definitions.  Of course, we cannot use this mechanism to define the
     biconditional itself, since it hasn't been introduced yet.  Instead, we
     use a more general form of definition, described as follows.

     In its most general form, a definition is simply an assertion that
     introduces a new symbol (or a new combination of existing symbols, as in
     ~ df-3an ) that is eliminable and does not strengthen the existing
     language.  The latter requirement means that the set of provable
     statements not containing the new symbol (or new combination) should
     remain exactly the same after the definition is introduced.  Our
     definition of the biconditional may look unusual compared to most
     definitions, but it strictly satisfies these requirements.

     The justification for our definition is that if we mechanically replace
     ` ( ph <-> ps ) ` (the definiendum i.e. the thing being defined) with
     ` -. ( ( ph -> ps ) -> -. ( ps -> ph ) ) ` (the definiens i.e. the
     defining expression) in the definition, the definition becomes the
     previously proved theorem ~ bijust .  It is impossible to use ~ df-bi to
     prove any statement expressed in the original language that can't be
     proved from the original axioms, because if we simply replace each
     instance of ~ df-bi in the proof with the corresponding ~ bijust instance,
     we will end up with a proof from the original axioms.

     Note that from Metamath's point of view, a definition is just another
     axiom - i.e. an assertion we claim to be true - but from our high level
     point of view, we are are not strengthening the language.  To indicate
     this fact, we prefix definition labels with "df-" instead of "ax-".  (This
     prefixing is an informal convention that means nothing to the Metamath
     proof verifier; it is just for human readability.)

     See ~ dfbi1 , ~ dfbi2 , and ~ dfbi3 for theorems suggesting typical
     textbook definitions of ` <-> ` , showing that our definition has the
     properties we expect.  Theorem ~ dfbi shows this definition rewritten in
     an abbreviated form after conjunction is introduced, for easier
     understanding. $)
  df-bi $a |- -. ( ( ( ph <-> ps ) -> -. ( ( ph -> ps ) -> -. ( ps -> ph ) ) )
        -> -. ( -. ( ( ph -> ps ) -> -. ( ps -> ph ) ) -> ( ph <-> ps ) ) ) $.

  $( Property of the biconditional connective. $)
  bi1 $p |- ( ( ph <-> ps ) -> ( ph -> ps ) ) $=
    ( wb wi wn df-bi simplim ax-mp syl ) ABCZABDZBADEZDEZKJMDZMJDEZDENABFNOGHKL
    GI $.
    $( [11-May-1999] $)

  $( Property of the biconditional connective. $)
  bi3 $p |- ( ( ph -> ps ) -> ( ( ps -> ph ) -> ( ph <-> ps ) ) ) $=
    ( wi wb wn df-bi simprim ax-mp expi ) ABCZBACZABDZLJKECEZCZMLCZECEOABFNOGHI
    $.
    $( [11-May-1999] $)

  ${
    impbii.1 $e |- ( ph -> ps ) $.
    impbii.2 $e |- ( ps -> ph ) $.
    $( Infer an equivalence from an implication and its converse. $)
    impbii $p |- ( ph <-> ps ) $=
      ( wi wb bi3 mp2 ) ABEBAEABFCDABGH $.
      $( [5-Aug-1993] $)
  $}

  ${
    impbidd.1 $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
    impbidd.2 $e |- ( ph -> ( ps -> ( th -> ch ) ) ) $.
    $( Deduce an equivalence from two implications.  (Contributed by Rodolfo
       Medina, 12-Oct-2010.) $)
    impbidd $p |- ( ph -> ( ps -> ( ch <-> th ) ) ) $=
      ( wi wb bi3 syl6c ) ABCDGDCGCDHEFCDIJ $.
      $( [12-Oct-2010] $)
  $}

  ${
    impbid21d.1 $e |- ( ps -> ( ch -> th ) ) $.
    impbid21d.2 $e |- ( ph -> ( th -> ch ) ) $.
    $( Deduce an equivalence from two implications.  (Contributed by Wolf
       Lammen, 12-May-2013.) $)
    impbid21d $p |- ( ph -> ( ps -> ( ch <-> th ) ) ) $=
      ( wi a1i a1d impbidd ) ABCDBCDGGAEHADCGBFIJ $.
      $( [12-May-2013] $)
  $}

  ${
    impbid.1 $e |- ( ph -> ( ps -> ch ) ) $.
    impbid.2 $e |- ( ph -> ( ch -> ps ) ) $.
    $( Deduce an equivalence from two implications.  (Dependency on df-an
       removed by Wolf Lammen, 3-Nov-2012.) $)
    impbid $p |- ( ph -> ( ps <-> ch ) ) $=
      ( wb impbid21d pm2.43i ) ABCFAABCDEGH $.
      $( [3-Nov-2012] $) $( [5-Aug-1993] $)
  $}

  $( Relate the biconditional connective to primitive connectives.  See
     ~ dfbi1gb for an unusual version proved directly from axioms. $)
  dfbi1 $p |- ( ( ph <-> ps ) <-> -. ( ( ph -> ps ) -> -. ( ps -> ph ) ) ) $=
    ( wb wi wn df-bi simplim ax-mp bi3 impi impbii ) ABCZABDZBADZEDEZLODZOLDEZD
    EPABFPQGHMNLABIJK $.
    $( [11-Nov-2012] $) $( [5-Aug-1993] $)

  $( This proof of ~ dfbi1 , discovered by Gregory Bush on 8-Mar-2004, has
     several curious properties.  First, it has only 17 steps directly from the
     axioms and ~ df-bi , compared to over 800 steps were the proof of ~ dfbi1
     expanded into axioms.  Second, step 2 demands only the property of "true";
     any axiom (or theorem) could be used.  It might be thought, therefore,
     that it is in some sense redundant, but in fact no proof is shorter than
     this (measured by number of steps).  Third, it illustrates how
     intermediate steps can "blow up" in size even in short proofs.  Fourth,
     the compressed proof is only 182 bytes (or 17 bytes in D-proof notation),
     but the generated web page is over 200kB with intermediate steps that are
     essentially incomprehensible to humans (other than Gregory Bush).  If
     there were an obfuscated code contest for proofs, this would be a
     contender. $)
  dfbi1gb $p |- ( ( ph <-> ps ) <-> -. ( ( ph -> ps ) -> -. ( ps -> ph ) ) ) $=
    ( wch wth wb wi wn df-bi ax-1 ax-mp ax-3 ax-2 ) ABEZABFBAFGFGZFNMFGFGZMNEZA
    BHCDCFFZOPFZCDIRGZQGZFZQRFSPOFZSFZFZUASUBISUCTFZFZUDUAFUEUFTGZUCGZFZUEUHUIM
    NHUHUGIJTUCKJUESIJSUCTLJJRQKJJJ $.
    $( [10-Mar-2004] $)

  ${
    biimpi.1 $e |- ( ph <-> ps ) $.
    $( Infer an implication from a logical equivalence. $)
    biimpi $p |- ( ph -> ps ) $=
      ( wb wi bi1 ax-mp ) ABDABECABFG $.
      $( [5-Aug-1993] $)
  $}

  ${
    sylbi.1 $e |- ( ph <-> ps ) $.
    sylbi.2 $e |- ( ps -> ch ) $.
    $( A mixed syllogism inference from a biconditional and an implication.
       Useful for substituting an antecedent with a definition. $)
    sylbi $p |- ( ph -> ch ) $=
      ( biimpi syl ) ABCABDFEG $.
      $( [5-Aug-1993] $)
  $}

  ${
    sylib.1 $e |- ( ph -> ps ) $.
    sylib.2 $e |- ( ps <-> ch ) $.
    $( A mixed syllogism inference from an implication and a biconditional. $)
    sylib $p |- ( ph -> ch ) $=
      ( biimpi syl ) ABCDBCEFG $.
      $( [5-Aug-1993] $)
  $}

  $( Property of the biconditional connective.  (The proof was shortened by
     Wolf Lammen, 11-Nov-2012.) $)
  bi2 $p |- ( ( ph <-> ps ) -> ( ps -> ph ) ) $=
    ( wb wi wn dfbi1 simprim sylbi ) ABCABDZBADZEDEJABFIJGH $.
    $( [11-Nov-2012] $) $( [11-May-1999] $)

  $( Commutative law for equivalence.  (Contributed by Wolf Lammen,
     10-Nov-2012.) $)
  bicom1 $p |- ( ( ph <-> ps ) -> ( ps <-> ph ) ) $=
    ( wb bi2 bi1 impbid ) ABCBAABDABEF $.
    $( [10-Nov-2012] $)

  $( Commutative law for equivalence.  Theorem *4.21 of [WhiteheadRussell]
     p. 117. $)
  bicom $p |- ( ( ph <-> ps ) <-> ( ps <-> ph ) ) $=
    ( wb bicom1 impbii ) ABCBACABDBADE $.
    $( [11-Nov-2012] $) $( [5-Aug-1993] $)

  ${
    bicomd.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Commute two sides of a biconditional in a deduction. $)
    bicomd $p |- ( ph -> ( ch <-> ps ) ) $=
      ( wb bicom sylib ) ABCECBEDBCFG $.
      $( [5-Aug-1993] $)
  $}

  ${
    bicomi.1 $e |- ( ph <-> ps ) $.
    $( Inference from commutative law for logical equivalence. $)
    bicomi $p |- ( ps <-> ph ) $=
      ( wb bicom1 ax-mp ) ABDBADCABEF $.
      $( [16-Sep-2013] $) $( [5-Aug-1993] $)
  $}

  ${
    impbid1.1 $e |- ( ph -> ( ps -> ch ) ) $.
    impbid1.2 $e |- ( ch -> ps ) $.
    $( Infer an equivalence from two implications. $)
    impbid1 $p |- ( ph -> ( ps <-> ch ) ) $=
      ( wi a1i impbid ) ABCDCBFAEGH $.
      $( [6-Mar-2007] $)
  $}

  ${
    impbid2.1 $e |- ( ps -> ch ) $.
    impbid2.2 $e |- ( ph -> ( ch -> ps ) ) $.
    $( Infer an equivalence from two implications.  (The proof was shortened by
       Wolf Lammen, 27-Sep-2013.) $)
    impbid2 $p |- ( ph -> ( ps <-> ch ) ) $=
      ( impbid1 bicomd ) ACBACBEDFG $.
      $( [27-Sep-2013] $) $( [6-Mar-2007] $)
  $}

  ${
    impcon4bid.1 $e |- ( ph -> ( ps -> ch ) ) $.
    impcon4bid.2 $e |- ( ph -> ( -. ps -> -. ch ) ) $.
    $( A variation on ~ impbid with contraposition.  (Contributed by Jeff
       Hankins, 3-Jul-2009.) $)
    impcon4bid $p |- ( ph -> ( ps <-> ch ) ) $=
      ( con4d impbid ) ABCDABCEFG $.
      $( [3-Jul-2009] $)
  $}

  ${
    biimpri.1 $e |- ( ph <-> ps ) $.
    $( Infer a converse implication from a logical equivalence.  (The proof was
       shortened by Wolf Lammen, 16-Sep-2013.) $)
    biimpri $p |- ( ps -> ph ) $=
      ( bicomi biimpi ) BAABCDE $.
      $( [16-Sep-2013] $) $( [5-Aug-1993] $)
  $}

  ${
    biimpd.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Deduce an implication from a logical equivalence. $)
    biimpd $p |- ( ph -> ( ps -> ch ) ) $=
      ( wb wi bi1 syl ) ABCEBCFDBCGH $.
      $( [5-Aug-1993] $)
  $}

  ${
    mpbi.min $e |- ph $.
    mpbi.maj $e |- ( ph <-> ps ) $.
    $( An inference from a biconditional, related to modus ponens. $)
    mpbi $p |- ps $=
      ( biimpi ax-mp ) ABCABDEF $.
      $( [5-Aug-1993] $)
  $}

  ${
    mpbir.min $e |- ps $.
    mpbir.maj $e |- ( ph <-> ps ) $.
    $( An inference from a biconditional, related to modus ponens. $)
    mpbir $p |- ph $=
      ( biimpri ax-mp ) BACABDEF $.
      $( [5-Aug-1993] $)
  $}

  ${
    mpbid.min $e |- ( ph -> ps ) $.
    mpbid.maj $e |- ( ph -> ( ps <-> ch ) ) $.
    $( A deduction from a biconditional, related to modus ponens. $)
    mpbid $p |- ( ph -> ch ) $=
      ( biimpd mpd ) ABCDABCEFG $.
      $( [5-Aug-1993] $)
  $}

  ${
    mpbii.min $e |- ps $.
    mpbii.maj $e |- ( ph -> ( ps <-> ch ) ) $.
    $( An inference from a nested biconditional, related to modus ponens.  (The
       proof was shortened by Wolf Lammen, 25-Oct-2012.) $)
    mpbii $p |- ( ph -> ch ) $=
      ( a1i mpbid ) ABCBADFEG $.
      $( [25-Oct-2012] $) $( [5-Aug-1993] $)
  $}

  ${
    sylibr.1 $e |- ( ph -> ps ) $.
    sylibr.2 $e |- ( ch <-> ps ) $.
    $( A mixed syllogism inference from an implication and a biconditional.
       Useful for substituting a consequent with a definition. $)
    sylibr $p |- ( ph -> ch ) $=
      ( biimpri syl ) ABCDCBEFG $.
      $( [5-Aug-1993] $)
  $}

  ${
    sylbir.1 $e |- ( ps <-> ph ) $.
    sylbir.2 $e |- ( ps -> ch ) $.
    $( A mixed syllogism inference from a biconditional and an implication. $)
    sylbir $p |- ( ph -> ch ) $=
      ( biimpri syl ) ABCBADFEG $.
      $( [5-Aug-1993] $)
  $}

  ${
    sylibd.1 $e |- ( ph -> ( ps -> ch ) ) $.
    sylibd.2 $e |- ( ph -> ( ch <-> th ) ) $.
    $( A syllogism deduction. $)
    sylibd $p |- ( ph -> ( ps -> th ) ) $=
      ( biimpd syld ) ABCDEACDFGH $.
      $( [3-Aug-1994] $)
  $}

  ${
    sylbid.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    sylbid.2 $e |- ( ph -> ( ch -> th ) ) $.
    $( A syllogism deduction. $)
    sylbid $p |- ( ph -> ( ps -> th ) ) $=
      ( biimpd syld ) ABCDABCEGFH $.
      $( [3-Aug-1994] $)
  $}

  ${
    mpbidi.min $e |- ( th -> ( ph -> ps ) ) $.
    mpbidi.maj $e |- ( ph -> ( ps <-> ch ) ) $.
    $( A deduction from a biconditional, related to modus ponens. $)
    mpbidi $p |- ( th -> ( ph -> ch ) ) $=
      ( biimpd sylcom ) DABCEABCFGH $.
      $( [9-Aug-1994] $)
  $}

  ${
    syl5bi.1 $e |- ( ph <-> ps ) $.
    syl5bi.2 $e |- ( ch -> ( ps -> th ) ) $.
    $( A mixed syllogism inference from a nested implication and a
       biconditional.  Useful for substituting an embedded antecedent with a
       definition. $)
    syl5bi $p |- ( ch -> ( ph -> th ) ) $=
      ( biimpi syl5 ) ABCDABEGFH $.
      $( [5-Aug-1993] $)
  $}

  ${
    syl5bir.1 $e |- ( ps <-> ph ) $.
    syl5bir.2 $e |- ( ch -> ( ps -> th ) ) $.
    $( A mixed syllogism inference from a nested implication and a
       biconditional. $)
    syl5bir $p |- ( ch -> ( ph -> th ) ) $=
      ( biimpri syl5 ) ABCDBAEGFH $.
      $( [5-Aug-1993] $)
  $}

  ${
    syl5ib.1 $e |- ( ph -> ps ) $.
    syl5ib.2 $e |- ( ch -> ( ps <-> th ) ) $.
    $( A mixed syllogism inference. $)
    syl5ib $p |- ( ch -> ( ph -> th ) ) $=
      ( biimpd syl5 ) ABCDECBDFGH $.
      $( [5-Aug-1993] $)

    $( A mixed syllogism inference. $)
    syl5ibcom $p |- ( ph -> ( ch -> th ) ) $=
      ( syl5ib com12 ) CADABCDEFGH $.
      $( [19-Jun-2007] $)
  $}

  ${
    syl5ibr.1 $e |- ( ph -> th ) $.
    syl5ibr.2 $e |- ( ch -> ( ps <-> th ) ) $.
    $( A mixed syllogism inference. $)
    syl5ibr $p |- ( ch -> ( ph -> ps ) ) $=
      ( bicomd syl5ib ) ADCBECBDFGH $.
      $( [22-Sep-2013] $) $( [3-Apr-1994] $)

    $( A mixed syllogism inference. $)
    syl5ibrcom $p |- ( ph -> ( ch -> ps ) ) $=
      ( syl5ibr com12 ) CABABCDEFGH $.
      $( [20-Jun-2007] $)
  $}

  ${
    biimprd.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Deduce a converse implication from a logical equivalence.  (The proof
       was shortened by Wolf Lammen, 22-Sep-2013.) $)
    biimprd $p |- ( ph -> ( ch -> ps ) ) $=
      ( id syl5ibr ) CBACCEDF $.
      $( [22-Sep-2013] $) $( [5-Aug-1993] $)
  $}

  ${
    biimpcd.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Deduce a commuted implication from a logical equivalence.  (The proof
       was shortened by Wolf Lammen, 22-Sep-2013.) $)
    biimpcd $p |- ( ps -> ( ph -> ch ) ) $=
      ( id syl5ibcom ) BBACBEDF $.
      $( [22-Sep-2013] $) $( [3-May-1994] $)

    $( Deduce a converse commuted implication from a logical equivalence.  (The
       proof was shortened by Wolf Lammen, 20-Dec-2013.) $)
    biimprcd $p |- ( ch -> ( ph -> ps ) ) $=
      ( id syl5ibrcom ) CBACCEDF $.
      $( [20-Dec-2013] $) $( [3-May-1994] $)
  $}

  ${
    syl6ib.1 $e |- ( ph -> ( ps -> ch ) ) $.
    syl6ib.2 $e |- ( ch <-> th ) $.
    $( A mixed syllogism inference from a nested implication and a
       biconditional. $)
    syl6ib $p |- ( ph -> ( ps -> th ) ) $=
      ( biimpi syl6 ) ABCDECDFGH $.
      $( [5-Aug-1993] $)
  $}

  ${
    syl6ibr.1 $e |- ( ph -> ( ps -> ch ) ) $.
    syl6ibr.2 $e |- ( th <-> ch ) $.
    $( A mixed syllogism inference from a nested implication and a
       biconditional.  Useful for substituting an embedded consequent with a
       definition. $)
    syl6ibr $p |- ( ph -> ( ps -> th ) ) $=
      ( biimpri syl6 ) ABCDEDCFGH $.
      $( [5-Aug-1993] $)
  $}


  ${
    syl6bi.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    syl6bi.2 $e |- ( ch -> th ) $.
    $( A mixed syllogism inference. $)
    syl6bi $p |- ( ph -> ( ps -> th ) ) $=
      ( biimpd syl6 ) ABCDABCEGFH $.
      $( [2-Jan-1994] $)
  $}

  ${
    syl6bir.1 $e |- ( ph -> ( ch <-> ps ) ) $.
    syl6bir.2 $e |- ( ch -> th ) $.
    $( A mixed syllogism inference. $)
    syl6bir $p |- ( ph -> ( ps -> th ) ) $=
      ( biimprd syl6 ) ABCDACBEGFH $.
      $( [18-May-1994] $)
  $}

  ${
    syl7bi.1 $e |- ( ph <-> ps ) $.
    syl7bi.2 $e |- ( ch -> ( th -> ( ps -> ta ) ) ) $.
    $( A mixed syllogism inference from a doubly nested implication and a
       biconditional. $)
    syl7bi $p |- ( ch -> ( th -> ( ph -> ta ) ) ) $=
      ( biimpi syl7 ) ABCDEABFHGI $.
      $( [5-Aug-1993] $)
  $}

  ${
    syl8ib.1 $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
    syl8ib.2 $e |- ( th <-> ta ) $.
    $( A syllogism rule of inference.  The second premise is used to replace
       the consequent of the first premise. $)
    syl8ib $p |- ( ph -> ( ps -> ( ch -> ta ) ) ) $=
      ( biimpi syl8 ) ABCDEFDEGHI $.
      $( [1-Aug-1994] $)
  $}

  ${
    mpbird.min $e |- ( ph -> ch ) $.
    mpbird.maj $e |- ( ph -> ( ps <-> ch ) ) $.
    $( A deduction from a biconditional, related to modus ponens. $)
    mpbird $p |- ( ph -> ps ) $=
      ( biimprd mpd ) ACBDABCEFG $.
      $( [5-Aug-1993] $)
  $}

  ${
    mpbiri.min $e |- ch $.
    mpbiri.maj $e |- ( ph -> ( ps <-> ch ) ) $.
    $( An inference from a nested biconditional, related to modus ponens.  (The
       proof was shortened by Wolf Lammen, 25-Oct-2012.) $)
    mpbiri $p |- ( ph -> ps ) $=
      ( a1i mpbird ) ABCCADFEG $.
      $( [25-Oct-2012] $) $( [5-Aug-1993] $)
  $}

  ${
    sylibrd.1 $e |- ( ph -> ( ps -> ch ) ) $.
    sylibrd.2 $e |- ( ph -> ( th <-> ch ) ) $.
    $( A syllogism deduction. $)
    sylibrd $p |- ( ph -> ( ps -> th ) ) $=
      ( biimprd syld ) ABCDEADCFGH $.
      $( [3-Aug-1994] $)
  $}

  ${
    sylbird.1 $e |- ( ph -> ( ch <-> ps ) ) $.
    sylbird.2 $e |- ( ph -> ( ch -> th ) ) $.
    $( A syllogism deduction. $)
    sylbird $p |- ( ph -> ( ps -> th ) ) $=
      ( biimprd syld ) ABCDACBEGFH $.
      $( [3-Aug-1994] $)
  $}

  $( Principle of identity for logical equivalence.  Theorem *4.2 of
     [WhiteheadRussell] p. 117. $)
  biid $p |- ( ph <-> ph ) $=
    ( id impbii ) AAABZDC $.
    $( [5-Aug-1993] $)

  $( Principle of identity with antecedent. $)
  biidd $p |- ( ph -> ( ps <-> ps ) ) $=
    ( wb biid a1i ) BBCABDE $.
    $( [25-Nov-1995] $)

  $( Two propositions are equivalent if they are both true.  Closed form of
     ~ 2th .  Equivalent to a ~ bi1 -like version of the xor-connective.  This
     theorem stays true, no matter how you permute its operands.  This is
     evident from its sharper version
     ` ( ph <-> ( ps <-> ( ph <-> ps ) ) ) ` .  (Contributed by Wolf Lammen,
     12-May-2013.) $)
  pm5.1im $p |- ( ph -> ( ps -> ( ph <-> ps ) ) ) $=
    ( ax-1 impbid21d ) ABABBACABCD $.
    $( [12-May-2013] $)

  ${
    2th.1 $e |- ph $.
    2th.2 $e |- ps $.
    $( Two truths are equivalent. $)
    2th $p |- ( ph <-> ps ) $=
      ( a1i impbii ) ABBADEABCEF $.
      $( [18-Aug-1993] $)
  $}

  ${
    2thd.1 $e |- ( ph -> ps ) $.
    2thd.2 $e |- ( ph -> ch ) $.
    $( Two truths are equivalent (deduction rule). $)
    2thd $p |- ( ph -> ( ps <-> ch ) ) $=
      ( wb pm5.1im sylc ) ABCBCFDEBCGH $.
      $( [29-Jan-2013] $) $( [3-Jun-2012] $)
  $}

  ${
    ibi.1 $e |- ( ph -> ( ph <-> ps ) ) $.
    $( Inference that converts a biconditional implied by one of its arguments,
       into an implication. $)
    ibi $p |- ( ph -> ps ) $=
      ( biimpd pm2.43i ) ABAABCDE $.
      $( [17-Oct-2003] $)
  $}

  ${
    ibir.1 $e |- ( ph -> ( ps <-> ph ) ) $.
    $( Inference that converts a biconditional implied by one of its arguments,
       into an implication. $)
    ibir $p |- ( ph -> ps ) $=
      ( bicomd ibi ) ABABACDE $.
      $( [22-Jul-2004] $)
  $}

  ${
    ibd.1 $e |- ( ph -> ( ps -> ( ps <-> ch ) ) ) $.
    $( Deduction that converts a biconditional implied by one of its arguments,
       into an implication. $)
    ibd $p |- ( ph -> ( ps -> ch ) ) $=
      ( wb bi1 syli ) BABCECDBCFG $.
      $( [26-Jun-2004] $)
  $}

  $( Distribution of implication over biconditional.  Theorem *5.74 of
     [WhiteheadRussell] p. 126.  (The proof was shortened by Wolf Lammen,
     11-Apr-2013.) $)
  pm5.74 $p |- ( ( ph -> ( ps <-> ch ) ) <->
               ( ( ph -> ps ) <-> ( ph -> ch ) ) ) $=
    ( wb wi bi1 imim3i bi2 impbid pm2.86d impbidd impbii ) ABCDZEZABEZACEZDZNOP
    MBCABCFGMCBABCHGIQABCQABCOPFJQACBOPHJKL $.
    $( [11-Apr-2013] $) $( [1-Aug-1994] $)

  ${
    pm5.74i.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Distribution of implication over biconditional (inference rule). $)
    pm5.74i $p |- ( ( ph -> ps ) <-> ( ph -> ch ) ) $=
      ( wb wi pm5.74 mpbi ) ABCEFABFACFEDABCGH $.
      $( [1-Aug-1994] $)
  $}

  ${
    pm5.74ri.1 $e |- ( ( ph -> ps ) <-> ( ph -> ch ) ) $.
    $( Distribution of implication over biconditional (reverse inference
       rule). $)
    pm5.74ri $p |- ( ph -> ( ps <-> ch ) ) $=
      ( wb wi pm5.74 mpbir ) ABCEFABFACFEDABCGH $.
      $( [1-Aug-1994] $)
  $}

  ${
    pm5.74d.1 $e |- ( ph -> ( ps -> ( ch <-> th ) ) ) $.
    $( Distribution of implication over biconditional (deduction rule). $)
    pm5.74d $p |- ( ph -> ( ( ps -> ch ) <-> ( ps -> th ) ) ) $=
      ( wb wi pm5.74 sylib ) ABCDFGBCGBDGFEBCDHI $.
      $( [21-Mar-1996] $)
  $}

  ${
    pm5.74rd.1 $e |- ( ph -> ( ( ps -> ch ) <-> ( ps -> th ) ) ) $.
    $( Distribution of implication over biconditional (deduction rule). $)
    pm5.74rd $p |- ( ph -> ( ps -> ( ch <-> th ) ) ) $=
      ( wi wb pm5.74 sylibr ) ABCFBDFGBCDGFEBCDHI $.
      $( [19-Mar-1997] $)
  $}

  ${
    bitri.1 $e |- ( ph <-> ps ) $.
    bitri.2 $e |- ( ps <-> ch ) $.
    $( An inference from transitive law for logical equivalence.  (The proof
       was shortened by Wolf Lammen, 13-Oct-2012.) $)
    bitri $p |- ( ph <-> ch ) $=
      ( biimpi sylib biimpri sylibr impbii ) ACABCABDFEGCBABCEHDIJ $.
      $( [13-Oct-2012] $) $( [5-Aug-1993] $)
  $}

  ${
    bitr2i.1 $e |- ( ph <-> ps ) $.
    bitr2i.2 $e |- ( ps <-> ch ) $.
    $( An inference from transitive law for logical equivalence. $)
    bitr2i $p |- ( ch <-> ph ) $=
      ( bitri bicomi ) ACABCDEFG $.
      $( [5-Aug-1993] $)
  $}

  ${
    bitr3i.1 $e |- ( ps <-> ph ) $.
    bitr3i.2 $e |- ( ps <-> ch ) $.
    $( An inference from transitive law for logical equivalence. $)
    bitr3i $p |- ( ph <-> ch ) $=
      ( bicomi bitri ) ABCBADFEG $.
      $( [5-Aug-1993] $)
  $}

  ${
    bitr4i.1 $e |- ( ph <-> ps ) $.
    bitr4i.2 $e |- ( ch <-> ps ) $.
    $( An inference from transitive law for logical equivalence. $)
    bitr4i $p |- ( ph <-> ch ) $=
      ( bicomi bitri ) ABCDCBEFG $.
      $( [5-Aug-1993] $)
  $}

  ${
    bitrd.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    bitrd.2 $e |- ( ph -> ( ch <-> th ) ) $.
    $( Deduction form of ~ bitri .  (The proof was shortened by Wolf Lammen,
       14-Apr-2013.) $)
    bitrd $p |- ( ph -> ( ps <-> th ) ) $=
      ( wi pm5.74i bitri pm5.74ri ) ABDABGACGADGABCEHACDFHIJ $.
      $( [14-Apr-2013] $) $( [5-Aug-1993] $)
  $}

  ${
    bitr2d.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    bitr2d.2 $e |- ( ph -> ( ch <-> th ) ) $.
    $( Deduction form of ~ bitr2i . $)
    bitr2d $p |- ( ph -> ( th <-> ps ) ) $=
      ( bitrd bicomd ) ABDABCDEFGH $.
      $( [9-Jun-2004] $)
  $}

  ${
    bitr3d.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    bitr3d.2 $e |- ( ph -> ( ps <-> th ) ) $.
    $( Deduction form of ~ bitr3i . $)
    bitr3d $p |- ( ph -> ( ch <-> th ) ) $=
      ( bicomd bitrd ) ACBDABCEGFH $.
      $( [5-Aug-1993] $)
  $}

  ${
    bitr4d.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    bitr4d.2 $e |- ( ph -> ( th <-> ch ) ) $.
    $( Deduction form of ~ bitr4i . $)
    bitr4d $p |- ( ph -> ( ps <-> th ) ) $=
      ( bicomd bitrd ) ABCDEADCFGH $.
      $( [5-Aug-1993] $)
  $}

  ${
    syl5bb.1 $e |- ( ph <-> ps ) $.
    syl5bb.2 $e |- ( ch -> ( ps <-> th ) ) $.
    $( A syllogism inference from two biconditionals. $)
    syl5bb $p |- ( ch -> ( ph <-> th ) ) $=
      ( wb a1i bitrd ) CABDABGCEHFI $.
      $( [5-Aug-1993] $)
  $}

  ${
    syl5rbb.1 $e |- ( ph <-> ps ) $.
    syl5rbb.2 $e |- ( ch -> ( ps <-> th ) ) $.
    $( A syllogism inference from two biconditionals. $)
    syl5rbb $p |- ( ch -> ( th <-> ph ) ) $=
      ( syl5bb bicomd ) CADABCDEFGH $.
      $( [5-Aug-1993] $)
  $}

  ${
    syl5bbr.1 $e |- ( ps <-> ph ) $.
    syl5bbr.2 $e |- ( ch -> ( ps <-> th ) ) $.
    $( A syllogism inference from two biconditionals. $)
    syl5bbr $p |- ( ch -> ( ph <-> th ) ) $=
      ( bicomi syl5bb ) ABCDBAEGFH $.
      $( [5-Aug-1993] $)
  $}

  ${
    syl5rbbr.1 $e |- ( ps <-> ph ) $.
    syl5rbbr.2 $e |- ( ch -> ( ps <-> th ) ) $.
    $( A syllogism inference from two biconditionals. $)
    syl5rbbr $p |- ( ch -> ( th <-> ph ) ) $=
      ( bicomi syl5rbb ) ABCDBAEGFH $.
      $( [25-Nov-1994] $)
  $}

  ${
    syl6bb.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    syl6bb.2 $e |- ( ch <-> th ) $.
    $( A syllogism inference from two biconditionals. $)
    syl6bb $p |- ( ph -> ( ps <-> th ) ) $=
      ( wb a1i bitrd ) ABCDECDGAFHI $.
      $( [5-Aug-1993] $)
  $}

  ${
    syl6rbb.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    syl6rbb.2 $e |- ( ch <-> th ) $.
    $( A syllogism inference from two biconditionals. $)
    syl6rbb $p |- ( ph -> ( th <-> ps ) ) $=
      ( syl6bb bicomd ) ABDABCDEFGH $.
      $( [5-Aug-1993] $)
  $}

  ${
    syl6bbr.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    syl6bbr.2 $e |- ( th <-> ch ) $.
    $( A syllogism inference from two biconditionals. $)
    syl6bbr $p |- ( ph -> ( ps <-> th ) ) $=
      ( bicomi syl6bb ) ABCDEDCFGH $.
      $( [5-Aug-1993] $)
  $}

  ${
    syl6rbbr.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    syl6rbbr.2 $e |- ( th <-> ch ) $.
    $( A syllogism inference from two biconditionals. $)
    syl6rbbr $p |- ( ph -> ( th <-> ps ) ) $=
      ( bicomi syl6rbb ) ABCDEDCFGH $.
      $( [25-Nov-1994] $)
  $}

  ${
    3imtr3.1 $e |- ( ph -> ps ) $.
    3imtr3.2 $e |- ( ph <-> ch ) $.
    3imtr3.3 $e |- ( ps <-> th ) $.
    $( A mixed syllogism inference, useful for removing a definition from both
       sides of an implication. $)
    3imtr3i $p |- ( ch -> th ) $=
      ( sylbir sylib ) CBDCABFEHGI $.
      $( [10-Aug-1994] $)
  $}

  ${
    3imtr4.1 $e |- ( ph -> ps ) $.
    3imtr4.2 $e |- ( ch <-> ph ) $.
    3imtr4.3 $e |- ( th <-> ps ) $.
    $( A mixed syllogism inference, useful for applying a definition to both
       sides of an implication. $)
    3imtr4i $p |- ( ch -> th ) $=
      ( sylbi sylibr ) CBDCABFEHGI $.
      $( [5-Aug-1993] $)
  $}

  ${
    3imtr3d.1 $e |- ( ph -> ( ps -> ch ) ) $.
    3imtr3d.2 $e |- ( ph -> ( ps <-> th ) ) $.
    3imtr3d.3 $e |- ( ph -> ( ch <-> ta ) ) $.
    $( More general version of ~ 3imtr3i .  Useful for converting conditional
       definitions in a formula. $)
    3imtr3d $p |- ( ph -> ( th -> ta ) ) $=
      ( sylibd sylbird ) ADBEGABCEFHIJ $.
      $( [8-Apr-1996] $)
  $}

  ${
    3imtr4d.1 $e |- ( ph -> ( ps -> ch ) ) $.
    3imtr4d.2 $e |- ( ph -> ( th <-> ps ) ) $.
    3imtr4d.3 $e |- ( ph -> ( ta <-> ch ) ) $.
    $( More general version of ~ 3imtr4i .  Useful for converting conditional
       definitions in a formula. $)
    3imtr4d $p |- ( ph -> ( th -> ta ) ) $=
      ( sylibrd sylbid ) ADBEGABCEFHIJ $.
      $( [26-Oct-1995] $)
  $}

  ${
    3imtr3g.1 $e |- ( ph -> ( ps -> ch ) ) $.
    3imtr3g.2 $e |- ( ps <-> th ) $.
    3imtr3g.3 $e |- ( ch <-> ta ) $.
    $( More general version of ~ 3imtr3i .  Useful for converting definitions
       in a formula.  (The proof was shortened by Wolf Lammen, 20-Dec-2013.) $)
    3imtr3g $p |- ( ph -> ( th -> ta ) ) $=
      ( syl5bir syl6ib ) ADCEDBACGFIHJ $.
      $( [20-Dec-2013] $) $( [20-May-1996] $)
  $}

  ${
    3imtr4g.1 $e |- ( ph -> ( ps -> ch ) ) $.
    3imtr4g.2 $e |- ( th <-> ps ) $.
    3imtr4g.3 $e |- ( ta <-> ch ) $.
    $( More general version of ~ 3imtr4i .  Useful for converting definitions
       in a formula.  (The proof was shortened by Wolf Lammen, 20-Dec-2013.) $)
    3imtr4g $p |- ( ph -> ( th -> ta ) ) $=
      ( syl5bi syl6ibr ) ADCEDBACGFIHJ $.
      $( [20-Dec-2013] $) $( [20-May-1996] $)
  $}

  ${
    3bitri.1 $e |- ( ph <-> ps ) $.
    3bitri.2 $e |- ( ps <-> ch ) $.
    3bitri.3 $e |- ( ch <-> th ) $.
    $( A chained inference from transitive law for logical equivalence. $)
    3bitri $p |- ( ph <-> th ) $=
      ( bitri ) ABDEBCDFGHH $.
      $( [5-Aug-1993] $)

    $( A chained inference from transitive law for logical equivalence. $)
    3bitrri $p |- ( th <-> ph ) $=
      ( bitr2i bitr3i ) DCAGABCEFHI $.
      $( [4-Aug-2006] $)
  $}

  ${
    3bitr2i.1 $e |- ( ph <-> ps ) $.
    3bitr2i.2 $e |- ( ch <-> ps ) $.
    3bitr2i.3 $e |- ( ch <-> th ) $.
    $( A chained inference from transitive law for logical equivalence. $)
    3bitr2i $p |- ( ph <-> th ) $=
      ( bitr4i bitri ) ACDABCEFHGI $.
      $( [4-Aug-2006] $)

    $( A chained inference from transitive law for logical equivalence. $)
    3bitr2ri $p |- ( th <-> ph ) $=
      ( bitr4i bitr2i ) ACDABCEFHGI $.
      $( [4-Aug-2006] $)
  $}

  ${
    3bitr3i.1 $e |- ( ph <-> ps ) $.
    3bitr3i.2 $e |- ( ph <-> ch ) $.
    3bitr3i.3 $e |- ( ps <-> th ) $.
    $( A chained inference from transitive law for logical equivalence. $)
    3bitr3i $p |- ( ch <-> th ) $=
      ( bitr3i bitri ) CBDCABFEHGI $.
      $( [19-Aug-1993] $)

    $( A chained inference from transitive law for logical equivalence. $)
    3bitr3ri $p |- ( th <-> ch ) $=
      ( bitr3i ) DBCGBACEFHH $.
      $( [5-Aug-1993] $)
  $}

  ${
    3bitr4i.1 $e |- ( ph <-> ps ) $.
    3bitr4i.2 $e |- ( ch <-> ph ) $.
    3bitr4i.3 $e |- ( th <-> ps ) $.
    $( A chained inference from transitive law for logical equivalence.  This
       inference is frequently used to apply a definition to both sides of a
       logical equivalence. $)
    3bitr4i $p |- ( ch <-> th ) $=
      ( bitr4i bitri ) CADFABDEGHI $.
      $( [5-Aug-1993] $)

    $( A chained inference from transitive law for logical equivalence. $)
    3bitr4ri $p |- ( th <-> ch ) $=
      ( bitr4i bitr2i ) CADFABDEGHI $.
      $( [2-Sep-1995] $)
  $}

  ${
    3bitrd.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    3bitrd.2 $e |- ( ph -> ( ch <-> th ) ) $.
    3bitrd.3 $e |- ( ph -> ( th <-> ta ) ) $.
    $( Deduction from transitivity of biconditional. $)
    3bitrd $p |- ( ph -> ( ps <-> ta ) ) $=
      ( bitrd ) ABDEABCDFGIHI $.
      $( [13-Aug-1999] $)

    $( Deduction from transitivity of biconditional. $)
    3bitrrd $p |- ( ph -> ( ta <-> ps ) ) $=
      ( bitr2d bitr3d ) ADEBHABCDFGIJ $.
      $( [4-Aug-2006] $)
  $}

  ${
    3bitr2d.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    3bitr2d.2 $e |- ( ph -> ( th <-> ch ) ) $.
    3bitr2d.3 $e |- ( ph -> ( th <-> ta ) ) $.
    $( Deduction from transitivity of biconditional. $)
    3bitr2d $p |- ( ph -> ( ps <-> ta ) ) $=
      ( bitr4d bitrd ) ABDEABCDFGIHJ $.
      $( [4-Aug-2006] $)

    $( Deduction from transitivity of biconditional. $)
    3bitr2rd $p |- ( ph -> ( ta <-> ps ) ) $=
      ( bitr4d bitr2d ) ABDEABCDFGIHJ $.
      $( [4-Aug-2006] $)
  $}

  ${
    3bitr3d.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    3bitr3d.2 $e |- ( ph -> ( ps <-> th ) ) $.
    3bitr3d.3 $e |- ( ph -> ( ch <-> ta ) ) $.
    $( Deduction from transitivity of biconditional.  Useful for converting
       conditional definitions in a formula. $)
    3bitr3d $p |- ( ph -> ( th <-> ta ) ) $=
      ( bitr3d bitrd ) ADCEABDCGFIHJ $.
      $( [24-Apr-1996] $)

    $( Deduction from transitivity of biconditional. $)
    3bitr3rd $p |- ( ph -> ( ta <-> th ) ) $=
      ( bitr3d ) ACEDHABCDFGII $.
      $( [4-Aug-2006] $)
  $}

  ${
    3bitr4d.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    3bitr4d.2 $e |- ( ph -> ( th <-> ps ) ) $.
    3bitr4d.3 $e |- ( ph -> ( ta <-> ch ) ) $.
    $( Deduction from transitivity of biconditional.  Useful for converting
       conditional definitions in a formula. $)
    3bitr4d $p |- ( ph -> ( th <-> ta ) ) $=
      ( bitr4d bitrd ) ADBEGABCEFHIJ $.
      $( [18-Oct-1995] $)

    $( Deduction from transitivity of biconditional. $)
    3bitr4rd $p |- ( ph -> ( ta <-> th ) ) $=
      ( bitr4d ) AEBDAECBHFIGI $.
      $( [4-Aug-2006] $)
  $}

  ${
    3bitr3g.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    3bitr3g.2 $e |- ( ps <-> th ) $.
    3bitr3g.3 $e |- ( ch <-> ta ) $.
    $( More general version of ~ 3bitr3i .  Useful for converting definitions
       in a formula. $)
    3bitr3g $p |- ( ph -> ( th <-> ta ) ) $=
      ( syl5bbr syl6bb ) ADCEDBACGFIHJ $.
      $( [4-Jun-1995] $)
  $}

  ${
    3bitr4g.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    3bitr4g.2 $e |- ( th <-> ps ) $.
    3bitr4g.3 $e |- ( ta <-> ch ) $.
    $( More general version of ~ 3bitr4i .  Useful for converting definitions
       in a formula. $)
    3bitr4g $p |- ( ph -> ( th <-> ta ) ) $=
      ( syl5bb syl6bbr ) ADCEDBACGFIHJ $.
      $( [5-Aug-1993] $)
  $}

  ${
    bi3ant.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Construct a bi-conditional in antecedent position.  (Contributed by Wolf
       Lammen, 14-May-2013.) $)
    bi3ant $p |- ( ( ( th -> ta ) -> ph ) -> ( ( ( ta -> th ) -> ps ) ->
                                                ( ( th <-> ta ) -> ch ) ) ) $=
      ( wi wb bi1 imim1i bi2 imim3i syl2im ) DEGZAGDEHZAGEDGZBGOBGOCGONADEIJOPB
      DEKJABCOFLM $.
      $( [14-May-2013] $)
  $}

  $( Express symmetries of theorems in terms of biconditionals.  (Contributed
     by Wolf Lammen, 14-May-2013.) $)
  bisym $p |- ( ( ( ph -> ps ) -> ( ch -> th ) ) -> ( ( ( ps -> ph )
      -> ( th -> ch ) ) -> ( ( ph <-> ps ) -> ( ch <-> th ) ) ) ) $=
    ( wi wb bi3 bi3ant ) CDEDCECDFABCDGH $.
    $( [14-May-2013] $)

  $( Double negation.  Theorem *4.13 of [WhiteheadRussell] p. 117. $)
  notnot $p |- ( ph <-> -. -. ph ) $=
    ( wn notnot1 notnot2 impbii ) AABBACADE $.
    $( [5-Aug-1993] $)

  $( Contraposition.  Theorem *4.1 of [WhiteheadRussell] p. 116. $)
  con34b $p |- ( ( ph -> ps ) <-> ( -. ps -> -. ph ) ) $=
    ( wi wn con3 ax-3 impbii ) ABCBDADCABEBAFG $.
    $( [5-Aug-1993] $)

  ${
    con4bid.1 $e |- ( ph -> ( -. ps <-> -. ch ) ) $.
    $( A contraposition deduction. $)
    con4bid $p |- ( ph -> ( ps <-> ch ) ) $=
      ( wn biimprd con4d biimpd impcon4bid ) ABCACBABEZCEZDFGAJKDHI $.
      $( [17-Sep-2013] $) $( [21-May-1994] $)
  $}

  ${
    notbid.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Deduction negating both sides of a logical equivalence. $)
    notbid $p |- ( ph -> ( -. ps <-> -. ch ) ) $=
      ( wn notnot 3bitr3g con4bid ) ABEZCEZABCIEJEDBFCFGH $.
      $( [17-Sep-2013] $) $( [21-May-1994] $)
  $}

  $( Contraposition.  Theorem *4.11 of [WhiteheadRussell] p. 117.  (The proof
     was shortened by Wolf Lammen, 12-Jun-2013.) $)
  notbi $p |- ( ( ph <-> ps ) <-> ( -. ph <-> -. ps ) ) $=
    ( wb wn id notbid con4bid impbii ) ABCZADBDCZIABIEFJABJEGH $.
    $( [12-Jun-2013] $) $( [21-May-1994] $)

  ${
    notbii.1 $e |- ( ph <-> ps ) $.
    $( Negate both sides of a logical equivalence.  (The proof was shortened by
       Wolf Lammen, 19-May-2013.) $)
    notbii $p |- ( -. ph <-> -. ps ) $=
      ( wb wn notbi mpbi ) ABDAEBEDCABFG $.
      $( [19-May-2013] $) $( [5-Aug-1993] $)
  $}

  ${
    con4bii.1 $e |- ( -. ph <-> -. ps ) $.
    $( A contraposition inference. $)
    con4bii $p |- ( ph <-> ps ) $=
      ( wb wn notbi mpbir ) ABDAEBEDCABFG $.
      $( [21-May-1994] $)
  $}

  ${
    mtbi.1 $e |- -. ph $.
    mtbi.2 $e |- ( ph <-> ps ) $.
    $( An inference from a biconditional, related to modus tollens.  (The proof
       was shortened by Wolf Lammen, 25-Oct-2012.) $)
    mtbi $p |- -. ps $=
      ( biimpri mto ) BACABDEF $.
      $( [25-Oct-2012] $) $( [15-Nov-1994] $)
  $}

  ${
    mtbir.1 $e |- -. ps $.
    mtbir.2 $e |- ( ph <-> ps ) $.
    $( An inference from a biconditional, related to modus tollens.  (The proof
       was shortened by Wolf Lammen, 14-Oct-2012.) $)
    mtbir $p |- -. ph $=
      ( bicomi mtbi ) BACABDEF $.
      $( [13-Oct-2012] $) $( [15-Nov-1994] $)
  $}

  ${
    mtbid.min $e |- ( ph -> -. ps ) $.
    mtbid.maj $e |- ( ph -> ( ps <-> ch ) ) $.
    $( A deduction from a biconditional, similar to modus tollens. $)
    mtbid $p |- ( ph -> -. ch ) $=
      ( biimprd mtod ) ACBDABCEFG $.
      $( [26-Nov-1995] $)
  $}

  ${
    mtbird.min $e |- ( ph -> -. ch ) $.
    mtbird.maj $e |- ( ph -> ( ps <-> ch ) ) $.
    $( A deduction from a biconditional, similar to modus tollens. $)
    mtbird $p |- ( ph -> -. ps ) $=
      ( biimpd mtod ) ABCDABCEFG $.
      $( [10-May-1994] $)
  $}

  ${
    mtbii.min $e |- -. ps $.
    mtbii.maj $e |- ( ph -> ( ps <-> ch ) ) $.
    $( An inference from a biconditional, similar to modus tollens. $)
    mtbii $p |- ( ph -> -. ch ) $=
      ( biimprd mtoi ) ACBDABCEFG $.
      $( [27-Nov-1995] $)
  $}

  ${
    mtbiri.min $e |- -. ch $.
    mtbiri.maj $e |- ( ph -> ( ps <-> ch ) ) $.
    $( An inference from a biconditional, similar to modus tollens. $)
    mtbiri $p |- ( ph -> -. ps ) $=
      ( biimpd mtoi ) ABCDABCEFG $.
      $( [24-Aug-1995] $)
  $}

  ${
    sylnib.1 $e |- ( ph -> -. ps ) $.
    sylnib.2 $e |- ( ps <-> ch ) $.
    $( A mixed syllogism inference from an implication and a biconditional.
       (Contributed by Wolf Lammen, 16-Dec-2013.) $)
    sylnib $p |- ( ph -> -. ch ) $=
      ( wb a1i mtbid ) ABCDBCFAEGH $.
      $( [16-Dec-2013] $)
  $}

  ${
    sylnibr.1 $e |- ( ph -> -. ps ) $.
    sylnibr.2 $e |- ( ch <-> ps ) $.
    $( A mixed syllogism inference from an implication and a biconditional.
       Useful for substituting an consequent with a definition.  (Contributed
       by Wolf Lammen, 16-Dec-2013.) $)
    sylnibr $p |- ( ph -> -. ch ) $=
      ( bicomi sylnib ) ABCDCBEFG $.
      $( [16-Dec-2013] $)
  $}

  ${
    sylnbi.1 $e |- ( ph <-> ps ) $.
    sylnbi.2 $e |- ( -. ps -> ch ) $.
    $( A mixed syllogism inference from a biconditional and an implication.
       Useful for substituting an antecedent with a definition.  (Contributed
       by Wolf Lammen, 16-Dec-2013.) $)
    sylnbi $p |- ( -. ph -> ch ) $=
      ( wn notbii sylbi ) AFBFCABDGEH $.
      $( [16-Dec-2013] $)
  $}

  ${
    sylnbir.1 $e |- ( ps <-> ph ) $.
    sylnbir.2 $e |- ( -. ps -> ch ) $.
    $( A mixed syllogism inference from a biconditional and an implication.
       (Contributed by Wolf Lammen, 16-Dec-2013.) $)
    sylnbir $p |- ( -. ph -> ch ) $=
      ( bicomi sylnbi ) ABCBADFEG $.
      $( [16-Dec-2013] $)
  $}

  ${
    xchnxbi.1 $e |- ( -. ph <-> ps ) $.
    xchnxbi.2 $e |- ( ph <-> ch ) $.
    $( Replacement of a subexpression by an equivalent one.  (Contributed by
       Wolf Lammen, 27-Sep-2014.) $)
    xchnxbi $p |- ( -. ch <-> ps ) $=
      ( wn notbii bitr3i ) CFAFBACEGDH $.
      $( [27-Sep-2014] $)
  $}

  ${
    xchnxbir.1 $e |- ( -. ph <-> ps ) $.
    xchnxbir.2 $e |- ( ch <-> ph ) $.
    $( Replacement of a subexpression by an equivalent one.  (Contributed by
       Wolf Lammen, 27-Sep-2014.) $)
    xchnxbir $p |- ( -. ch <-> ps ) $=
      ( bicomi xchnxbi ) ABCDCAEFG $.
      $( [27-Sep-2014] $)
  $}

  ${
    xchbinx.1 $e |- ( ph <-> -. ps ) $.
    xchbinx.2 $e |- ( ps <-> ch ) $.
    $( Replacement of a subexpression by an equivalent one.  (Contributed by
       Wolf Lammen, 27-Sep-2014.) $)
    xchbinx $p |- ( ph <-> -. ch ) $=
      ( wn notbii bitri ) ABFCFDBCEGH $.
      $( [27-Sep-2014] $)
  $}

  ${
    xchbinxr.1 $e |- ( ph <-> -. ps ) $.
    xchbinxr.2 $e |- ( ch <-> ps ) $.
    $( Replacement of a subexpression by an equivalent one.  (Contributed by
       Wolf Lammen, 27-Sep-2014.) $)
    xchbinxr $p |- ( ph <-> -. ch ) $=
      ( bicomi xchbinx ) ABCDCBEFG $.
      $( [27-Sep-2014] $)
  $}

  $( The next three rules are useful for building up wff's around a
     definition, in order to make use of the definition. $)

  ${
    bi.a $e |- ( ph <-> ps ) $.
    $( Introduce an antecedent to both sides of a logical equivalence.  (The
       proof was shortened by Wolf Lammen, 6-Feb-2013.) $)
    imbi2i $p |- ( ( ch -> ph ) <-> ( ch -> ps ) ) $=
      ( wb a1i pm5.74i ) CABABECDFG $.
      $( [6-Feb-2013] $) $( [5-Aug-1993] $)
  $}

  ${
    bibi.a $e |- ( ph <-> ps ) $.
    $( Inference adding a biconditional to the left in an equivalence.  (The
       proof was shortened by Andrew Salmon, 7-May-2011.)  (The proof was
       shortened by Wolf Lammen, 16-May-2013.) $)
    bibi2i $p |- ( ( ch <-> ph ) <-> ( ch <-> ps ) ) $=
      ( wb id syl6bb syl6bbr impbii ) CAEZCBEZJCABJFDGKCBAKFDHI $.
      $( [16-May-2013] $) $( [5-Aug-1993] $)

    $( Inference adding a biconditional to the right in an equivalence. $)
    bibi1i $p |- ( ( ph <-> ch ) <-> ( ps <-> ch ) ) $=
      ( wb bicom bibi2i 3bitri ) ACECAECBEBCEACFABCDGCBFH $.
      $( [5-Aug-1993] $)

    ${
      bibi12.2 $e |- ( ch <-> th ) $.
      $( The equivalence of two equivalences. $)
      bibi12i $p |- ( ( ph <-> ch ) <-> ( ps <-> th ) ) $=
        ( wb bibi2i bibi1i bitri ) ACGADGBDGCDAFHABDEIJ $.
        $( [5-Aug-1993] $)
    $}
  $}

  ${
    imbid.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Deduction adding an antecedent to both sides of a logical
       equivalence. $)
    imbi2d $p |- ( ph -> ( ( th -> ps ) <-> ( th -> ch ) ) ) $=
      ( wb a1d pm5.74d ) ADBCABCFDEGH $.
      $( [5-Aug-1993] $)

    $( Deduction adding a consequent to both sides of a logical equivalence.
       (The proof was shortened by Wolf Lammen, 17-Sep-2013.) $)
    imbi1d $p |- ( ph -> ( ( ps -> th ) <-> ( ch -> th ) ) ) $=
      ( wi biimprd imim1d biimpd impbid ) ABDFCDFACBDABCEGHABCDABCEIHJ $.
      $( [17-Sep-2013] $) $( [5-Aug-1993] $)

    $( Deduction adding a biconditional to the left in an equivalence.  (The
       proof was shortened by Wolf Lammen, 19-May-2013.) $)
    bibi2d $p |- ( ph -> ( ( th <-> ps ) <-> ( th <-> ch ) ) ) $=
      ( wb wi pm5.74i bibi2i pm5.74 3bitr4i pm5.74ri ) ADBFZDCFZADGZABGZFOACGZF
      AMGANGPQOABCEHIADBJADCJKL $.
      $( [19-May-2013] $) $( [5-Aug-1993] $)

    $( Deduction adding a biconditional to the right in an equivalence. $)
    bibi1d $p |- ( ph -> ( ( ps <-> th ) <-> ( ch <-> th ) ) ) $=
      ( wb bibi2d bicom 3bitr4g ) ADBFDCFBDFCDFABCDEGBDHCDHI $.
      $( [5-Aug-1993] $)
  $}

  ${
    imbi12d.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    imbi12d.2 $e |- ( ph -> ( th <-> ta ) ) $.
    $( Deduction joining two equivalences to form equivalence of
       implications. $)
    imbi12d $p |- ( ph -> ( ( ps -> th ) <-> ( ch -> ta ) ) ) $=
      ( wi imbi1d imbi2d bitrd ) ABDHCDHCEHABCDFIADECGJK $.
      $( [5-Aug-1993] $)
    $( Deduction joining two equivalences to form equivalence of
       biconditionals. $)
    bibi12d $p |- ( ph -> ( ( ps <-> th ) <-> ( ch <-> ta ) ) ) $=
      ( wb bibi1d bibi2d bitrd ) ABDHCDHCEHABCDFIADECGJK $.
      $( [5-Aug-1993] $)
  $}

  $( Theorem *4.84 of [WhiteheadRussell] p. 122. $)
  imbi1 $p |- ( ( ph <-> ps ) -> ( ( ph -> ch ) <-> ( ps -> ch ) ) ) $=
    ( wb id imbi1d ) ABDZABCGEF $.
    $( [3-Jan-2005] $)

  $( Theorem *4.85 of [WhiteheadRussell] p. 122.  (The proof was shortened by
     Wolf Lammen, 19-May-2013.) $)
  imbi2 $p |- ( ( ph <-> ps ) -> ( ( ch -> ph ) <-> ( ch -> ps ) ) ) $=
    ( wb id imbi2d ) ABDZABCGEF $.
    $( [19-May-2013] $) $( [3-Jan-2005] $)

  ${
    imbi1i.1 $e |- ( ph <-> ps ) $.
    $( Introduce a consequent to both sides of a logical equivalence.  (The
       proof was shortened by Wolf Lammen, 17-Sep-2013.) $)
    imbi1i $p |- ( ( ph -> ch ) <-> ( ps -> ch ) ) $=
      ( wb wi imbi1 ax-mp ) ABEACFBCFEDABCGH $.
      $( [17-Sep-2013] $) $( [5-Aug-1993] $)
  $}

  ${
    imbi12i.1 $e |- ( ph <-> ps ) $.
    imbi12i.2 $e |- ( ch <-> th ) $.
    $( Join two logical equivalences to form equivalence of implications. $)
    imbi12i $p |- ( ( ph -> ch ) <-> ( ps -> th ) ) $=
      ( wi imbi2i imbi1i bitri ) ACGADGBDGCDAFHABDEIJ $.
      $( [5-Aug-1993] $)
  $}

  $( Theorem *4.86 of [WhiteheadRussell] p. 122. $)
  bibi1 $p |- ( ( ph <-> ps ) -> ( ( ph <-> ch ) <-> ( ps <-> ch ) ) ) $=
    ( wb id bibi1d ) ABDZABCGEF $.
    $( [3-Jan-2005] $)

  $( Contraposition.  Theorem *4.12 of [WhiteheadRussell] p. 117.  (The proof
     was shortened by Wolf Lammen, 3-Jan-2013.) $)
  con2bi $p |- ( ( ph <-> -. ps ) <-> ( ps <-> -. ph ) ) $=
    ( wn wb notbi notnot bibi2i bicom 3bitr2i ) ABCZDACZJCZDKBDBKDAJEBLKBFGKBHI
    $.
    $( [3-Jan-2013] $) $( [15-Apr-1995] $)

  ${
    con2bid.1 $e |- ( ph -> ( ps <-> -. ch ) ) $.
    $( A contraposition deduction. $)
    con2bid $p |- ( ph -> ( ch <-> -. ps ) ) $=
      ( wn wb con2bi sylibr ) ABCEFCBEFDCBGH $.
      $( [15-Apr-1995] $)
  $}

  ${
    con1bid.1 $e |- ( ph -> ( -. ps <-> ch ) ) $.
    $( A contraposition deduction. $)
    con1bid $p |- ( ph -> ( -. ch <-> ps ) ) $=
      ( wn bicomd con2bid ) ABCEACBABECDFGF $.
      $( [9-Oct-1999] $)
  $}

  ${
    con1bii.1 $e |- ( -. ph <-> ps ) $.
    $( A contraposition inference.  (The proof was shortened by Wolf Lammen,
       13-Oct-2012.) $)
    con1bii $p |- ( -. ps <-> ph ) $=
      ( wn notnot xchbinx bicomi ) ABDAADBAECFG $.
      $( [28-Sep-2014] $) $( [5-Aug-1993] $)
  $}

  ${
    con1biiOLD.1 $e |- ( -. ph <-> ps ) $.
    $( Obsolete proof of ~ con1bii as of 28-Sep-2014. $)
    con1biiOLD $p |- ( -. ps <-> ph ) $=
      ( wn notnot notbii bitr2i ) AADZDBDAEHBCFG $.
      $( [13-Oct-2012] $) $( [5-Aug-1993] $)
  $}

  ${
    con2bii.1 $e |- ( ph <-> -. ps ) $.
    $( A contraposition inference. $)
    con2bii $p |- ( ps <-> -. ph ) $=
      ( wn bicomi con1bii ) ADBBAABDCEFE $.
      $( [5-Aug-1993] $)
  $}

  $( Contraposition.  Bidirectional version of ~ con1 . $)
  con1b $p |- ( ( -. ph -> ps ) <-> ( -. ps -> ph ) ) $=
    ( wn wi con1 impbii ) ACBDBCADABEBAEF $.
    $( [5-Aug-1993] $)

  $( Contraposition.  Bidirectional version of ~ con2 . $)
  con2b $p |- ( ( ph -> -. ps ) <-> ( ps -> -. ph ) ) $=
    ( wn wi con2 impbii ) ABCDBACDABEBAEF $.
    $( [5-Aug-1993] $)

  $( A wff is equivalent to itself with true antecedent. $)
  biimt $p |- ( ph -> ( ps <-> ( ph -> ps ) ) ) $=
    ( wi ax-1 pm2.27 impbid2 ) ABABCBADABEF $.
    $( [28-Jan-1996] $)

  $( Theorem *5.5 of [WhiteheadRussell] p. 125. $)
  pm5.5 $p |- ( ph -> ( ( ph -> ps ) <-> ps ) ) $=
    ( wi biimt bicomd ) ABABCABDE $.
    $( [3-Jan-2005] $)

  ${
    a1bi.1 $e |- ph $.
    $( Inference rule introducing a theorem as an antecedent.  The proof was
       shortened by Wolf Lammen, 11-Nov-2012.) $)
    a1bi $p |- ( ps <-> ( ph -> ps ) ) $=
      ( wi wb biimt ax-mp ) ABABDECABFG $.
      $( [11-Nov-2012] $) $( [5-Aug-1993] $)
  $}

  ${
    mt2bi.1 $e |- ph $.
    $( A false consequent falsifies an antecedent.  (The proof was shortened by
       Wolf Lammen, 12-Nov-2012.) $)
    mt2bi $p |- ( -. ps <-> ( ps -> -. ph ) ) $=
      ( wn wi a1bi con2b bitri ) BDZAIEBADEAICFABGH $.
      $( [12-Nov-2012] $) $( [19-Aug-1993] $)
  $}

  $( Modus-tollens-like theorem.  (The proof was shortened by Wolf Lammen,
     12-Nov-2012.) $)
  mtt $p |- ( -. ph -> ( -. ps <-> ( ps -> ph ) ) ) $=
    ( wn wi biimt con34b syl6bbr ) ACZBCZHIDBADHIEBAFG $.
    $( [12-Nov-2012] $) $( [7-Apr-2001] $)

  $( Theorem *5.501 of [WhiteheadRussell] p. 125. $)
  pm5.501 $p |- ( ph -> ( ps <-> ( ph <-> ps ) ) ) $=
    ( wb pm5.1im bi1 com12 impbid ) ABABCZABDHABABEFG $.
    $( [24-Jan-2013] $) $( [3-Jan-2005] $)

  $( Implication in terms of implication and biconditional.  (The proof was
     shortened by Wolf Lammen, 24-Jan-2013.) $)
  ibib $p |- ( ( ph -> ps ) <-> ( ph -> ( ph <-> ps ) ) ) $=
    ( wb pm5.501 pm5.74i ) ABABCABDE $.
    $( [24-Jan-2013] $) $( [31-Mar-1994] $)

  $( Implication in terms of implication and biconditional.  (The proof was
     shortened by Wolf Lammen, 21-Dec-2013.) $)
  ibibr $p |- ( ( ph -> ps ) <-> ( ph -> ( ps <-> ph ) ) ) $=
    ( wb pm5.501 bicom syl6bb pm5.74i ) ABBACZABABCHABDABEFG $.
    $( [21-Dec-2013] $) $( [29-Apr-2005] $)

  ${
    tbt.1 $e |- ph $.
    $( A wff is equivalent to its equivalence with truth.  (The proof was
       shortened by Andrew Salmon, 13-May-2011.) $)
    tbt $p |- ( ps <-> ( ps <-> ph ) ) $=
      ( wb ibibr pm5.74ri ax-mp ) ABBADZDCABHABEFG $.
      $( [16-May-2011] $) $( [18-Aug-1993] $)
  $}

  $( The negation of a wff is equivalent to the wff's equivalence to
     falsehood.  (Contributed by Juha Arpiainen, 19-Jan-2006.)  (The proof was
     shortened by Wolf Lammen, 28-Jan-2013.) $)
  nbn2 $p |- ( -. ph -> ( -. ps <-> ( ph <-> ps ) ) ) $=
    ( wn wb pm5.501 notbi syl6bbr ) ACZBCZHIDABDHIEABFG $.
    $( [28-Jan-2013] $) $( [19-Jan-2006] $)

  $( Transfer negation via an equivalence.  (The proof was shortened by Wolf
     Lammen, 28-Jan-2013.) $)
  bibif $p |- ( -. ps -> ( ( ph <-> ps ) <-> -. ph ) ) $=
    ( wn wb nbn2 bicom syl6rbb ) BCACBADABDBAEBAFG $.
    $( [28-Jan-2013] $) $( [3-Oct-2007] $)

  ${
    nbn.1 $e |- -. ph $.
    $( The negation of a wff is equivalent to the wff's equivalence to
       falsehood.  (The proof was shortened by Wolf Lammen, 3-Oct-2013.) $)
    nbn $p |- ( -. ps <-> ( ps <-> ph ) ) $=
      ( wb wn bibif ax-mp bicomi ) BADZBEZAEIJDCBAFGH $.
      $( [3-Oct-2013] $) $( [5-Aug-1993] $)
  $}

  ${
    nbn3.1 $e |- ph $.
    $( Transfer falsehood via equivalence. $)
    nbn3 $p |- ( -. ps <-> ( ps <-> -. ph ) ) $=
      ( wn notnoti nbn ) ADBACEF $.
      $( [11-Sep-2006] $)
  $}

  $( Two propositions are equivalent if they are both false.  Closed form of
     ~ 2false .  Equivalent to a ~ bi2 -like version of the xor-connective.
     (Contributed by Wolf Lammen, 13-May-2013.) $)
  pm5.21im $p |- ( -. ph -> ( -. ps -> ( ph <-> ps ) ) ) $=
    ( wn wb nbn2 biimpd ) ACBCABDABEF $.
    $( [13-May-2013] $)

  ${
    2false.1 $e |- -. ph $.
    2false.2 $e |- -. ps $.
    $( Two falsehoods are equivalent.  (The proof was shortened by Wolf Lammen,
       19-May-2013.) $)
    2false $p |- ( ph <-> ps ) $=
      ( wn 2th con4bii ) ABAEBECDFG $.
      $( [19-May-2013] $) $( [4-Apr-2005] $)
  $}

  ${
    2falsed.1 $e |- ( ph -> -. ps ) $.
    2falsed.2 $e |- ( ph -> -. ch ) $.
    $( Two falsehoods are equivalent (deduction rule). $)
    2falsed $p |- ( ph -> ( ps <-> ch ) ) $=
      ( pm2.21d impbid ) ABCABCDFACBEFG $.
      $( [11-Oct-2013] $)
  $}

  ${
    pm5.21ni.1 $e |- ( ph -> ps ) $.
    pm5.21ni.2 $e |- ( ch -> ps ) $.
    $( Two propositions implying a false one are equivalent.  (The proof was
       shortened by Wolf Lammen, 19-May-2013.) $)
    pm5.21ni $p |- ( -. ps -> ( ph <-> ch ) ) $=
      ( wn con3i 2falsed ) BFACABDGCBEGH $.
      $( [19-May-2013] $) $( [16-Feb-1996] $)

    ${
      pm5.21nii.3 $e |- ( ps -> ( ph <-> ch ) ) $.
      $( Eliminate an antecedent implied by each side of a biconditional. $)
      pm5.21nii $p |- ( ph <-> ch ) $=
        ( wb pm5.21ni pm2.61i ) BACGFABCDEHI $.
        $( [21-May-1999] $)
    $}
  $}

  ${
    pm5.21ndd.1 $e |- ( ph -> ( ch -> ps ) ) $.
    pm5.21ndd.2 $e |- ( ph -> ( th -> ps ) ) $.
    pm5.21ndd.3 $e |- ( ph -> ( ps -> ( ch <-> th ) ) ) $.
    $( Eliminate an antecedent implied by each side of a biconditional,
       deduction version.  (Contributed by Paul Chapman, 21-Nov-2012.)  ( The
       proof was shortened by Wolf Lammen, 6-Oct-2013.) $)
    pm5.21ndd $p |- ( ph -> ( ch <-> th ) ) $=
      ( wb wn con3d pm5.21im syl6c pm2.61d ) ABCDHZGABICIDINACBEJADBFJCDKLM $.
      $( [6-Oct-2013] $) $( [21-Nov-2012] $)
  $}

  ${
    bija.1 $e |- ( ph -> ( ps -> ch ) ) $.
    bija.2 $e |- ( -. ph -> ( -. ps -> ch ) ) $.
    $( Combine antecedents into a single bi-conditional.  This inference,
       reminiscent of ~ ja , is reversible:  The hypotheses can be deduced from
       the conclusion alone (see ~ pm5.1im and ~ pm5.21im ).  (Contributed by
       Wolf Lammen, 13-May-2013.) $)
    bija $p |- ( ( ph <-> ps ) -> ch ) $=
      ( wb bi2 syli wn bi1 con3d pm2.61d ) ABFZBCBMACABGDHBIMAICMABABJKEHL $.
      $( [13-May-2013] $)
  $}

  $( Theorem *5.18 of [WhiteheadRussell] p. 124.  This theorem says that
     logical equivalence is the same as negated "exclusive-or."  (The proof was
     shortened by Andrew Salmon, 20-Jun-2011.)  (The proof was shortened by
     Wolf Lammen, 15-Oct-2013.) $)
  pm5.18 $p |- ( ( ph <-> ps ) <-> -. ( ph <-> -. ps ) ) $=
    ( wb wn pm5.501 con1bid bitr2d nbn2 pm2.61i ) AABCZABDZCZDZCAMBJABLAKEFABEG
    ADZMKJNKLAKHFABHGI $.
    $( [15-Oct-2013] $) $( [28-Jun-2002] $)

  $( Two ways to express "exclusive or." $)
  xor3 $p |- ( -. ( ph <-> ps ) <-> ( ph <-> -. ps ) ) $=
    ( wn wb pm5.18 con2bii bicomi ) ABCDZABDZCIHABEFG $.
    $( [1-Jan-2006] $)

  $( Move negation outside of biconditional.  Compare Theorem *5.18 of
     [WhiteheadRussell] p. 124.  (The proof was shortened by Wolf Lammen,
     20-Sep-2013.) $)
  nbbn $p |- ( ( -. ph <-> ps ) <-> -. ( ph <-> ps ) ) $=
    ( wb wn xor3 con2bi bicom 3bitrri ) ABCDABDCBADZCIBCABEABFBIGH $.
    $( [20-Sep-2013] $) $( [27-Jun-2002] $)

  $( Associative law for the biconditional.  An axiom of system DS in Vladimir
     Lifschitz, "On calculational proofs", Annals of Pure and Applied Logic,
     113:207-224, 2002,
     ~ http://www.cs.utexas.edu/users/ai-lab/pub-view.php?PubID=26805 .
     Interestingly, this law was not included in _Principia Mathematica_ but
     was apparently first noted by Jan Lukasiewicz circa 1923.  (The proof was
     shortened by Juha Arpiainen, 19-Jan-2006.)  (The proof was shortened by
     Wolf Lammen, 21-Sep-2013.) $)
  biass $p |- ( ( ( ph <-> ps ) <-> ch ) <-> ( ph <-> ( ps <-> ch ) ) ) $=
    ( wb pm5.501 bibi1d bitr3d wn nbbn nbn2 syl5bbr pm2.61i ) AABDZCDZABCDZDZDA
    ONPABMCABEFAOEGAHZOHZNPRBHZCDQNBCIQSMCABJFKAOJGL $.
    $( [21-Sep-2013] $) $( [8-Jan-2005] $)

  $( Theorem *5.19 of [WhiteheadRussell] p. 124. $)
  pm5.19 $p |- -. ( ph <-> -. ph ) $=
    ( wb wn biid pm5.18 mpbi ) AABAACBCADAAEF $.
    $( [3-Jan-2005] $)

  $( Logical equivalence of commuted antecedents.  Part of Theorem *4.87 of
     [WhiteheadRussell] p. 122. $)
  bi2.04 $p |- ( ( ph -> ( ps -> ch ) ) <-> ( ps -> ( ph -> ch ) ) ) $=
    ( wi pm2.04 impbii ) ABCDDBACDDABCEBACEF $.
    $( [5-Aug-1993] $)

  $( Antecedent absorption implication.  Theorem *5.4 of [WhiteheadRussell]
     p. 125. $)
  pm5.4 $p |- ( ( ph -> ( ph -> ps ) ) <-> ( ph -> ps ) ) $=
    ( wi pm2.43 ax-1 impbii ) AABCZCGABDGAEF $.
    $( [5-Aug-1993] $)

  $( Distributive law for implication.  Compare Theorem *5.41 of
     [WhiteheadRussell] p. 125. $)
  imdi $p |- ( ( ph -> ( ps -> ch ) ) <->
               ( ( ph -> ps ) -> ( ph -> ch ) ) ) $=
    ( wi ax-2 pm2.86 impbii ) ABCDDABDACDDABCEABCFG $.
    $( [5-Aug-1993] $)

  $( Theorem *5.41 of [WhiteheadRussell] p. 125.  (The proof was shortened by
     Wolf Lammen, 12-Oct-2012.) $)
  pm5.41 $p |- ( ( ( ph -> ps ) -> ( ph -> ch ) ) <->
                ( ph -> ( ps -> ch ) ) ) $=
    ( wi imdi bicomi ) ABCDDABDACDDABCEF $.
    $( [13-Oct-2012] $) $( [3-Jan-2005] $)

  $( Theorem *4.8 of [WhiteheadRussell] p. 122. $)
  pm4.8 $p |- ( ( ph -> -. ph ) <-> -. ph ) $=
    ( wn wi pm2.01 ax-1 impbii ) AABZCGADGAEF $.
    $( [3-Jan-2005] $)

  $( Theorem *4.81 of [WhiteheadRussell] p. 122. $)
  pm4.81 $p |- ( ( -. ph -> ph ) <-> ph ) $=
    ( wn wi pm2.18 pm2.24 impbii ) ABACAADAAEF $.
    $( [3-Jan-2005] $)

  $( Simplify an implication between two implications when the antecedent of
     the first is a consequence of the antecedent of the second.  The reverse
     form is useful in producing the successor step in induction proofs.
     (Contributed by Paul Chapman, 22-Jun-2011.)  (The proof was shortened by
     Wolf Lammen, 14-Sep-2013.) $)
  imim21b $p |- ( ( ps -> ph ) -> ( ( ( ph -> ch ) -> ( ps -> th ) ) <->
                                    ( ps -> ( ch -> th ) ) ) ) $=
    ( wi bi2.04 wb pm5.5 imbi1d imim2i pm5.74d syl5bb ) ACEZBDEEBMDEZEBAEZBCDEZ
    EMBDFOBNPANPGBAMCDACHIJKL $.
    $( [14-Sep-2013] $) $( [22-Jun-2011] $)


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Logical disjunction and conjunction
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Declare connectives for disjunction ('or') and conjunction ('and'). $)
  $c \/ $. $( Vee (read:  'or') $)
  $c /\ $. $( Wedge (read:  'and') $)

  $( Extend wff definition to include disjunction ('or'). $)
  wo $a wff ( ph \/ ps ) $.
  $( Extend wff definition to include conjunction ('and'). $)
  wa $a wff ( ph /\ ps ) $.

  $( Define disjunction (logical 'or').  This is our first use of the
     biconditional connective in a definition; we use it in place of the
     traditional "<=def=>", which means the same thing, except that we can
     manipulate the biconditional connective directly in proofs rather than
     having to rely on an informal definition substitution rule.  Note that if
     we mechanically substitute ` ( -. ph -> ps ) ` for ` ( ph \/ ps ) ` , we
     end up with an instance of previously proved theorem ~ biid .  This is the
     justification for the definition, along with the fact that it introduces a
     new symbol ` \/ ` .  Definition of [Margaris] p. 49. $)
  df-or $a |- ( ( ph \/ ps ) <-> ( -. ph -> ps ) ) $.

  $( Define conjunction (logical 'and').  Definition of [Margaris] p. 49. $)
  df-an $a |- ( ( ph /\ ps ) <-> -. ( ph -> -. ps ) ) $.

  $( Theorem *4.64 of [WhiteheadRussell] p. 120. $)
  pm4.64 $p |- ( ( -. ph -> ps ) <-> ( ph \/ ps ) ) $=
    ( wo wn wi df-or bicomi ) ABCADBEABFG $.
    $( [3-Jan-2005] $)

  $( Theorem *2.53 of [WhiteheadRussell] p. 107. $)
  pm2.53 $p |- ( ( ph \/ ps ) -> ( -. ph -> ps ) ) $=
    ( wo wn wi df-or biimpi ) ABCADBEABFG $.
    $( [23-Jul-2012] $) $( [3-Jan-2005] $)

  $( Theorem *2.54 of [WhiteheadRussell] p. 107. $)
  pm2.54 $p |- ( ( -. ph -> ps ) -> ( ph \/ ps ) ) $=
    ( wo wn wi df-or biimpri ) ABCADBEABFG $.
    $( [3-Jan-2005] $)

  ${
    ori.1 $e |- ( ph \/ ps ) $.
    $( Infer implication from disjunction. $)
    ori $p |- ( -. ph -> ps ) $=
      ( wo wn wi df-or mpbi ) ABDAEBFCABGH $.
      $( [11-Jun-1994] $)
  $}

  ${
    orri.1 $e |- ( -. ph -> ps ) $.
    $( Infer implication from disjunction. $)
    orri $p |- ( ph \/ ps ) $=
      ( wo wn wi df-or mpbir ) ABDAEBFCABGH $.
      $( [11-Jun-1994] $)
  $}

  ${
    ord.1 $e |- ( ph -> ( ps \/ ch ) ) $.
    $( Deduce implication from disjunction. $)
    ord $p |- ( ph -> ( -. ps -> ch ) ) $=
      ( wo wn wi df-or sylib ) ABCEBFCGDBCHI $.
      $( [18-May-1994] $)
  $}

  ${
    orrd.1 $e |- ( ph -> ( -. ps -> ch ) ) $.
    $( Deduce implication from disjunction. $)
    orrd $p |- ( ph -> ( ps \/ ch ) ) $=
      ( wn wi wo pm2.54 syl ) ABECFBCGDBCHI $.
      $( [27-Nov-1995] $)
  $}

  ${
    jaoi.1 $e |- ( ph -> ps ) $.
    jaoi.2 $e |- ( ch -> ps ) $.
    $( Inference disjoining the antecedents of two implications. $)
    jaoi $p |- ( ( ph \/ ch ) -> ps ) $=
      ( wo wn pm2.53 syl6 pm2.61d2 ) ACFZABKAGCBACHEIDJ $.
      $( [13-Dec-2013] $) $( [5-Apr-1994] $)
  $}

  ${
    jaod.1 $e |- ( ph -> ( ps -> ch ) ) $.
    jaod.2 $e |- ( ph -> ( th -> ch ) ) $.
    $( Deduction disjoining the antecedents of two implications. $)
    jaod $p |- ( ph -> ( ( ps \/ th ) -> ch ) ) $=
      ( wo wi com12 jaoi ) BDGACBACHDABCEIADCFIJI $.
      $( [4-Apr-2013] $) $( [18-Aug-1994] $)
  $}

  $( Elimination of disjunction by denial of a disjunct.  Theorem *2.55 of
     [WhiteheadRussell] p. 107.  (The proof was shortened by Wolf Lammen,
     21-Jul-2012.) $)
  orel1 $p |- ( -. ph -> ( ( ph \/ ps ) -> ps ) ) $=
    ( wo wn pm2.53 com12 ) ABCADBABEF $.
    $( [23-Jul-2012] $) $( [12-Aug-1994] $)

  $( Elimination of disjunction by denial of a disjunct.  Theorem *2.56 of
     [WhiteheadRussell] p. 107.  (The proof was shortened by Wolf Lammen,
     5-Apr-2013.) $)
  orel2 $p |- ( -. ph -> ( ( ps \/ ph ) -> ps ) ) $=
    ( wn idd pm2.21 jaod ) ACZBBAGBDABEF $.
    $( [5-Apr-2013] $) $( [12-Aug-1994] $)

  $( Introduction of a disjunct.  Axiom *1.3 of [WhiteheadRussell] p. 96. $)
  olc $p |- ( ph -> ( ps \/ ph ) ) $=
    ( wn ax-1 orrd ) ABAABCDE $.
    $( [30-Aug-1993] $)

  $( Introduction of a disjunct.  Theorem *2.2 of [WhiteheadRussell] p. 104. $)
  orc $p |- ( ph -> ( ph \/ ps ) ) $=
    ( pm2.24 orrd ) AABABCD $.
    $( [30-Aug-1993] $)

  $( Axiom *1.4 of [WhiteheadRussell] p. 96. $)
  pm1.4 $p |- ( ( ph \/ ps ) -> ( ps \/ ph ) ) $=
    ( wo olc orc jaoi ) ABACBABDBAEF $.
    $( [15-Nov-2012] $) $( [3-Jan-2005] $)

  $( Commutative law for disjunction.  Theorem *4.31 of [WhiteheadRussell]
     p. 118.  (The proof was shortened by Wolf Lammen, 15-Nov-2012.) $)
  orcom $p |- ( ( ph \/ ps ) <-> ( ps \/ ph ) ) $=
    ( wo pm1.4 impbii ) ABCBACABDBADE $.
    $( [15-Nov-2012] $) $( [5-Aug-1993] $)

  ${
    orcomd.1 $e |- ( ph -> ( ps \/ ch ) ) $.
    $( Commutation of disjuncts in consequent. $)
    orcomd $p |- ( ph -> ( ch \/ ps ) ) $=
      ( wo orcom sylib ) ABCECBEDBCFG $.
      $( [2-Dec-2010] $)
  $}

  ${
    orcoms.1 $e |- ( ( ph \/ ps ) -> ch ) $.
    $( Commutation of disjuncts in antecedent. $)
    orcoms $p |- ( ( ps \/ ph ) -> ch ) $=
      ( wo pm1.4 syl ) BAEABECBAFDG $.
      $( [2-Dec-2012] $)
  $}

  ${
    orci.1 $e |- ph $.
    $( Deduction introducing a disjunct.  (The proof was shortened by Wolf
       Lammen, 14-Nov-2012.) $)
    orci $p |- ( ph \/ ps ) $=
      ( pm2.24i orri ) ABABCDE $.
      $( [14-Nov-2012] $) $( [19-Jan-2008] $)

    $( Deduction introducing a disjunct.  (The proof was shortened by Wolf
       Lammen, 14-Nov-2012.) $)
    olci $p |- ( ps \/ ph ) $=
      ( wn a1i orri ) BAABDCEF $.
      $( [14-Nov-2012] $) $( [19-Jan-2008] $)
  $}

  ${
    orcd.1 $e |- ( ph -> ps ) $.
    $( Deduction introducing a disjunct. $)
    orcd $p |- ( ph -> ( ps \/ ch ) ) $=
      ( wo orc syl ) ABBCEDBCFG $.
      $( [20-Sep-2007] $)

    $( Deduction introducing a disjunct.  (The proof was shortened by Wolf
       Lammen, 3-Oct-2013.) $)
    olcd $p |- ( ph -> ( ch \/ ps ) ) $=
      ( orcd orcomd ) ABCABCDEF $.
      $( [3-Oct-2013] $) $( [11-Apr-2008] $)
  $}

  ${
    orcs.1 $e |- ( ( ph \/ ps ) -> ch ) $.
    $( Deduction eliminating disjunct. _Notational convention_:  We sometimes
       suffix with "s" the label of an inference that manipulates an
       antecedent, leaving the consequent unchanged.  The "s" means that the
       inference eliminates the need for a syllogism ( ~ syl ) -type inference
       in a proof. $)
    orcs $p |- ( ph -> ch ) $=
      ( wo orc syl ) AABECABFDG $.
      $( [21-Jun-1994] $)
  $}

  ${
    olcs.1 $e |- ( ( ph \/ ps ) -> ch ) $.
    $( Deduction eliminating disjunct.  (The proof was shortened by Wolf
       Lammen, 3-Oct-2013.) $)
    olcs $p |- ( ps -> ch ) $=
      ( orcoms orcs ) BACABCDEF $.
      $( [3-Oct-2013] $) $( [21-Jun-1994] $)
  $}

  $( Theorem *2.07 of [WhiteheadRussell] p. 101. $)
  pm2.07 $p |- ( ph -> ( ph \/ ph ) ) $=
    ( olc ) AAB $.
    $( [3-Jan-2005] $)

  $( Theorem *2.45 of [WhiteheadRussell] p. 106. $)
  pm2.45 $p |- ( -. ( ph \/ ps ) -> -. ph ) $=
    ( wo orc con3i ) AABCABDE $.
    $( [3-Jan-2005] $)

  $( Theorem *2.46 of [WhiteheadRussell] p. 106. $)
  pm2.46 $p |- ( -. ( ph \/ ps ) -> -. ps ) $=
    ( wo olc con3i ) BABCBADE $.
    $( [3-Jan-2005] $)

  $( Theorem *2.47 of [WhiteheadRussell] p. 107. $)
  pm2.47 $p |- ( -. ( ph \/ ps ) -> ( -. ph \/ ps ) ) $=
    ( wo wn pm2.45 orcd ) ABCDADBABEF $.
    $( [3-Jan-2005] $)

  $( Theorem *2.48 of [WhiteheadRussell] p. 107. $)
  pm2.48 $p |- ( -. ( ph \/ ps ) -> ( ph \/ -. ps ) ) $=
    ( wo wn pm2.46 olcd ) ABCDBDAABEF $.
    $( [3-Jan-2005] $)

  $( Theorem *2.49 of [WhiteheadRussell] p. 107. $)
  pm2.49 $p |- ( -. ( ph \/ ps ) -> ( -. ph \/ -. ps ) ) $=
    ( wo wn pm2.46 olcd ) ABCDBDADABEF $.
    $( [3-Jan-2005] $)

  $( Slight generalization of Theorem *2.67 of [WhiteheadRussell] p. 107. $)
  pm2.67-2 $p |- ( ( ( ph \/ ch ) -> ps ) -> ( ph -> ps ) ) $=
    ( wo orc imim1i ) AACDBACEF $.
    $( [9-Dec-2012] $) $( [3-Jan-2005] $)

  $( Theorem *2.67 of [WhiteheadRussell] p. 107. $)
  pm2.67 $p |- ( ( ( ph \/ ps ) -> ps ) -> ( ph -> ps ) ) $=
    ( pm2.67-2 ) ABBC $.
    $( [9-Dec-2012] $) $( [3-Jan-2005] $)

  $( Theorem *2.25 of [WhiteheadRussell] p. 104. $)
  pm2.25 $p |- ( ph \/ ( ( ph \/ ps ) -> ps ) ) $=
    ( wo wi orel1 orri ) AABCBDABEF $.
    $( [3-Jan-2005] $)

  $( A wff is equivalent to its disjunction with falsehood.  Theorem *4.74 of
     [WhiteheadRussell] p. 121.  (The proof was shortened by Wolf Lammen,
     18-Nov-2012.) $)
  biorf $p |- ( -. ph -> ( ps <-> ( ph \/ ps ) ) ) $=
    ( wn wo olc orel1 impbid2 ) ACBABDBAEABFG $.
    $( [18-Nov-2012] $) $( [23-Mar-1995] $)

  $( A wff is equivalent to its negated disjunction with falsehood. $)
  biortn $p |- ( ph -> ( ps <-> ( -. ph \/ ps ) ) ) $=
    ( wn wo wb notnot1 biorf syl ) AACZCBIBDEAFIBGH $.
    $( [9-Jul-2012] $)

  ${
    biorfi.1 $e |- -. ph $.
    $( A wff is equivalent to its disjunction with falsehood. $)
    biorfi $p |- ( ps <-> ( ps \/ ph ) ) $=
      ( wn wo wb orc orel2 impbid2 ax-mp ) ADZBBAEZFCKBLBAGABHIJ $.
      $( [23-Mar-1995] $)
  $}

  $( Theorem *2.621 of [WhiteheadRussell] p. 107. $)
  pm2.621 $p |- ( ( ph -> ps ) -> ( ( ph \/ ps ) -> ps ) ) $=
    ( wi id idd jaod ) ABCZABBGDGBEF $.
    $( [13-Dec-2013] $) $( [3-Jan-2005] $)

  $( Theorem *2.62 of [WhiteheadRussell] p. 107.  (The proof was shortened by
     Wolf Lammen, 13-Dec-2013.) $)
  pm2.62 $p |- ( ( ph \/ ps ) -> ( ( ph -> ps ) -> ps ) ) $=
    ( wi wo pm2.621 com12 ) ABCABDBABEF $.
    $( [13-Dec-2013] $) $( [3-Jan-2005] $)

  $( Theorem *2.68 of [WhiteheadRussell] p. 108. $)
  pm2.68 $p |- ( ( ( ph -> ps ) -> ps ) -> ( ph \/ ps ) ) $=
    ( wi jarl orrd ) ABCBCABABBDE $.
    $( [21-Oct-2012] $) $( [3-Jan-2005] $)

  $( Logical 'or' expressed in terms of implication only.  Theorem *5.25 of
     [WhiteheadRussell] p. 124.  (The proof was shortened by Wolf Lammen,
     20-Oct-2012.) $)
  dfor2 $p |- ( ( ph \/ ps ) <-> ( ( ph -> ps ) -> ps ) ) $=
    ( wo wi pm2.62 pm2.68 impbii ) ABCABDBDABEABFG $.
    $( [21-Oct-2012] $) $( [12-Aug-2004] $)

  $( Implication in terms of disjunction.  Theorem *4.6 of [WhiteheadRussell]
     p. 120. $)
  imor $p |- ( ( ph -> ps ) <-> ( -. ph \/ ps ) ) $=
    ( wi wn wo notnot imbi1i df-or bitr4i ) ABCADZDZBCJBEAKBAFGJBHI $.
    $( [5-Aug-1993] $)

  ${
    imori.1 $e |- ( ph -> ps ) $.
    $( Infer disjunction from implication. $)
    imori $p |- ( -. ph \/ ps ) $=
      ( wi wn wo imor mpbi ) ABDAEBFCABGH $.
      $( [12-Mar-2012] $)
  $}

  ${
    imorri.1 $e |- ( -. ph \/ ps ) $.
    $( Infer implication from disjunction.  (Contributed by Jonathan Ben-Naim,
       3-Jun-2011.) $)
    imorri $p |- ( ph -> ps ) $=
      ( wi wn wo imor mpbir ) ABDAEBFCABGH $.
      $( [3-Jun-2011] $)
  $}

  $( Law of excluded middle, also called the principle of _tertium non datur_.
     Theorem *2.11 of [WhiteheadRussell] p. 101.  It says that something is
     either true or not true; there are no in-between values of truth.  This is
     an essential distinction of our classical logic and is not a theorem of
     intuitionistic logic. $)
  exmid $p |- ( ph \/ -. ph ) $=
    ( wn id orri ) AABZECD $.
    $( [5-Aug-1993] $)

  $( Theorem *2.1 of [WhiteheadRussell] p. 101.  (The proof was shortened by
     Wolf Lammen, 23-Nov-2012.) $)
  pm2.1 $p |- ( -. ph \/ ph ) $=
    ( id imori ) AAABC $.
    $( [23-Nov-2012] $) $( [3-Jan-2005] $)

  $( Theorem *2.13 of [WhiteheadRussell] p. 101. $)
  pm2.13 $p |- ( ph \/ -. -. -. ph ) $=
    ( wn notnot1 orri ) AABZBBECD $.
    $( [3-Jan-2005] $)

  $( Theorem *4.62 of [WhiteheadRussell] p. 120. $)
  pm4.62 $p |- ( ( ph -> -. ps ) <-> ( -. ph \/ -. ps ) ) $=
    ( wn imor ) ABCD $.
    $( [3-Jan-2005] $)

  $( Theorem *4.66 of [WhiteheadRussell] p. 120. $)
  pm4.66 $p |- ( ( -. ph -> -. ps ) <-> ( ph \/ -. ps ) ) $=
    ( wn pm4.64 ) ABCD $.
    $( [3-Jan-2005] $)

  $( Theorem *4.63 of [WhiteheadRussell] p. 120. $)
  pm4.63 $p |- ( -. ( ph -> -. ps ) <-> ( ph /\ ps ) ) $=
    ( wa wn wi df-an bicomi ) ABCABDEDABFG $.
    $( [3-Jan-2005] $)

  $( Express implication in terms of conjunction. $)
  imnan $p |- ( ( ph -> -. ps ) <-> -. ( ph /\ ps ) ) $=
    ( wa wn wi df-an con2bii ) ABCABDEABFG $.
    $( [9-Apr-1994] $)

  $( Express implication in terms of conjunction.  Theorem 3.4(27) of [Stoll]
     p. 176.  (The proof was shortened by Wolf Lammen, 30-Oct-2012.) $)
  iman $p |- ( ( ph -> ps ) <-> -. ( ph /\ -. ps ) ) $=
    ( wi wn wa notnot imbi2i imnan bitri ) ABCABDZDZCAJEDBKABFGAJHI $.
    $( [30-Oct-2012] $) $( [5-Aug-1993] $)

  $( Express conjunction in terms of implication. $)
  annim $p |- ( ( ph /\ -. ps ) <-> -. ( ph -> ps ) ) $=
    ( wi wn wa iman con2bii ) ABCABDEABFG $.
    $( [2-Aug-1994] $)

  $( Theorem *4.61 of [WhiteheadRussell] p. 120. $)
  pm4.61 $p |- ( -. ( ph -> ps ) <-> ( ph /\ -. ps ) ) $=
    ( wn wa wi annim bicomi ) ABCDABECABFG $.
    $( [3-Jan-2005] $)

  $( Theorem *4.65 of [WhiteheadRussell] p. 120. $)
  pm4.65 $p |- ( -. ( -. ph -> ps ) <-> ( -. ph /\ -. ps ) ) $=
    ( wn pm4.61 ) ACBD $.
    $( [3-Jan-2005] $)

  $( Theorem *4.67 of [WhiteheadRussell] p. 120. $)
  pm4.67 $p |- ( -. ( -. ph -> -. ps ) <-> ( -. ph /\ ps ) ) $=
    ( wn pm4.63 ) ACBD $.
    $( [3-Jan-2005] $)

  ${
    imp.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Importation inference.  (The proof was shortened by Eric Schmidt,
       22-Dec-2006.) $)
    imp $p |- ( ( ph /\ ps ) -> ch ) $=
      ( wa wn wi df-an impi sylbi ) ABEABFGFCABHABCDIJ $.
      $( [24-Mar-2013] $) $( [5-Aug-1993] $)

    $( Importation inference with commuted antecedents. $)
    impcom $p |- ( ( ps /\ ph ) -> ch ) $=
      ( com12 imp ) BACABCDEF $.
      $( [25-May-2005] $)
  $}

  ${
    imp3.1 $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
    $( Importation deduction. $)
    imp3a $p |- ( ph -> ( ( ps /\ ch ) -> th ) ) $=
      ( wa wi com3l imp com12 ) BCFADBCADGABCDEHIJ $.
      $( [24-Mar-2013] $) $( [31-Mar-1994] $)

    $( An importation inference. $)
    imp31 $p |- ( ( ( ph /\ ps ) /\ ch ) -> th ) $=
      ( wa wi imp ) ABFCDABCDGEHH $.
      $( [26-Apr-1994] $)

    $( An importation inference. $)
    imp32 $p |- ( ( ph /\ ( ps /\ ch ) ) -> th ) $=
      ( wa imp3a imp ) ABCFDABCDEGH $.
      $( [26-Apr-1994] $)
  $}

  ${
    exp.1 $e |- ( ( ph /\ ps ) -> ch ) $.
    $( Exportation inference.  (This theorem used to be labeled "exp" but was
       changed to "ex" so as not to conflict with the math token "exp", per the
       June 2006 Metamath spec change.)  (The proof was shortened by Eric
       Schmidt, 22-Dec-2006.) $)
    ex $p |- ( ph -> ( ps -> ch ) ) $=
      ( wn wi wa df-an sylbir expi ) ABCABEFEABGCABHDIJ $.
      $( [24-Mar-2013] $) $( [5-Aug-1993] $)

    $( Exportation inference with commuted antecedents. $)
    expcom $p |- ( ps -> ( ph -> ch ) ) $=
      ( ex com12 ) ABCABCDEF $.
      $( [25-May-2005] $)
  $}

  ${
    exp3a.1 $e |- ( ph -> ( ( ps /\ ch ) -> th ) ) $.
    $( Exportation deduction. $)
    exp3a $p |- ( ph -> ( ps -> ( ch -> th ) ) ) $=
      ( wi wa com12 ex com3r ) BCADBCADFABCGDEHIJ $.
      $( [24-Mar-2013] $) $( [20-Aug-1993] $)

    $( A deduction version of exportation, followed by importation. $)
    expdimp $p |- ( ( ph /\ ps ) -> ( ch -> th ) ) $=
      ( wi exp3a imp ) ABCDFABCDEGH $.
      $( [6-Sep-2008] $)
  $}

  ${
    impancom.1 $e |- ( ( ph /\ ps ) -> ( ch -> th ) ) $.
    $( Mixed importation/commutation inference. $)
    impancom $p |- ( ( ph /\ ch ) -> ( ps -> th ) ) $=
      ( wi ex com23 imp ) ACBDFABCDABCDFEGHI $.
      $( [22-Jun-2013] $)
  $}

  $( Theorem *3.3 (Exp) of [WhiteheadRussell] p. 112.  (The proof was shortened
     by Wolf Lammen, 24-Mar-2013.) $)
  pm3.3 $p |- ( ( ( ph /\ ps ) -> ch ) -> ( ph -> ( ps -> ch ) ) ) $=
    ( wa wi id exp3a ) ABDCEZABCHFG $.
    $( [24-Mar-2013] $) $( [3-Jan-2005] $)

  $( Theorem *3.31 (Imp) of [WhiteheadRussell] p. 112.  (The proof was
     shortened by Wolf Lammen, 24-Mar-2013.) $)
  pm3.31 $p |- ( ( ph -> ( ps -> ch ) ) -> ( ( ph /\ ps ) -> ch ) ) $=
    ( wi id imp3a ) ABCDDZABCGEF $.
    $( [24-Mar-2013] $) $( [3-Jan-2005] $)

  $( Import-export theorem.  Part of Theorem *4.87 of [WhiteheadRussell]
     p. 122.  (The proof was shortened by Wolf Lammen, 24-Mar-2013.) $)
  impexp $p |- ( ( ( ph /\ ps ) -> ch ) <-> ( ph -> ( ps -> ch ) ) ) $=
    ( wa wi pm3.3 pm3.31 impbii ) ABDCEABCEEABCFABCGH $.
    $( [24-Mar-2013] $) $( [5-Aug-1993] $)

  $( Join antecedents with conjunction.  Theorem *3.2 of [WhiteheadRussell]
     p. 111.  (The proof was shortened by Wolf Lammen, 12-Nov-2012.) $)
  pm3.2 $p |- ( ph -> ( ps -> ( ph /\ ps ) ) ) $=
    ( wa id ex ) ABABCZFDE $.
    $( [12-Nov-2012] $) $( [5-Aug-1993] $)

  $( Join antecedents with conjunction.  Theorem *3.21 of [WhiteheadRussell]
     p. 111. $)
  pm3.21 $p |- ( ph -> ( ps -> ( ps /\ ph ) ) ) $=
    ( wa pm3.2 com12 ) BABACBADE $.
    $( [5-Aug-1993] $)

  $( Theorem *3.22 of [WhiteheadRussell] p. 111.  (The proof was shortened by
     Wolf Lammen, 13-Nov-2012.) $)
  pm3.22 $p |- ( ( ph /\ ps ) -> ( ps /\ ph ) ) $=
    ( wa pm3.21 imp ) ABBACABDE $.
    $( [13-Nov-2012] $) $( [3-Jan-2005] $)

  $( Commutative law for conjunction.  Theorem *4.3 of [WhiteheadRussell]
     p. 118.  (The proof was shortened by Wolf Lammen, 4-Nov-2012.) $)
  ancom $p |- ( ( ph /\ ps ) <-> ( ps /\ ph ) ) $=
    ( wa pm3.22 impbii ) ABCBACABDBADE $.
    $( [4-Nov-2012] $) $( [25-Jun-1998] $)

  ${
    ancomd.1 $e |- ( ph -> ( ps /\ ch ) ) $.
    $( Commutation of conjuncts in consequent.  (Contributed by Jeff Hankins,
       14-Aug-2009.) $)
    ancomd $p |- ( ph -> ( ch /\ ps ) ) $=
      ( wa ancom sylib ) ABCECBEDBCFG $.
      $( [18-Apr-2010] $) $( [14-Aug-2009] $)
  $}

  ${
    ancoms.1 $e |- ( ( ph /\ ps ) -> ch ) $.
    $( Inference commuting conjunction in antecedent. $)
    ancoms $p |- ( ( ps /\ ph ) -> ch ) $=
      ( expcom imp ) BACABCDEF $.
      $( [21-Apr-1994] $)
  $}

  ${
    ancomsd.1 $e |- ( ph -> ( ( ps /\ ch ) -> th ) ) $.
    $( Deduction commuting conjunction in antecedent. $)
    ancomsd $p |- ( ph -> ( ( ch /\ ps ) -> th ) ) $=
      ( wa ancom syl5bi ) CBFBCFADCBGEH $.
      $( [12-Dec-2004] $)
  $}

  ${
    pm3.2i.1 $e |- ph $.
    pm3.2i.2 $e |- ps $.
    $( Infer conjunction of premises. $)
    pm3.2i $p |- ( ph /\ ps ) $=
      ( wa pm3.2 mp2 ) ABABECDABFG $.
      $( [5-Aug-1993] $)
  $}

  $( Nested conjunction of antecedents. $)
  pm3.43i $p |- ( ( ph -> ps ) ->
                ( ( ph -> ch ) -> ( ph -> ( ps /\ ch ) ) ) ) $=
    ( wa pm3.2 imim3i ) BCBCDABCEF $.
    $( [5-Aug-1993] $)

  $( Elimination of a conjunct.  Theorem *3.26 (Simp) of [WhiteheadRussell]
     p. 112.  (The proof was shortened by Wolf Lammen, 13-Nov-2012.) $)
  simpl $p |- ( ( ph /\ ps ) -> ph ) $=
    ( ax-1 imp ) ABAABCD $.
    $( [13-Nov-2012] $) $( [5-Aug-1993] $)

  ${
    simpli.1 $e |- ( ph /\ ps ) $.
    $( Inference eliminating a conjunct. $)
    simpli $p |- ph $=
      ( wa simpl ax-mp ) ABDACABEF $.
      $( [15-Jun-1994] $)
  $}

  ${
    simpld.1 $e |- ( ph -> ( ps /\ ch ) ) $.
    $( Deduction eliminating a conjunct. $)
    simpld $p |- ( ph -> ps ) $=
      ( wa simpl syl ) ABCEBDBCFG $.
      $( [5-Aug-1993] $)
  $}

  ${
    simplbi.1 $e |- ( ph <-> ( ps /\ ch ) ) $.
    $( Deduction eliminating a conjunct. $)
    simplbi $p |- ( ph -> ps ) $=
      ( wa biimpi simpld ) ABCABCEDFG $.
      $( [27-May-1998] $)
  $}

  $( Elimination of a conjunct.  Theorem *3.27 (Simp) of [WhiteheadRussell]
     p. 112.  (The proof was shortened by Wolf Lammen, 13-Nov-2012.) $)
  simpr $p |- ( ( ph /\ ps ) -> ps ) $=
    ( idd imp ) ABBABCD $.
    $( [13-Nov-2012] $)  $( [5-Aug-1993] $)

  ${
    simpri.1 $e |- ( ph /\ ps ) $.
    $( Inference eliminating a conjunct. $)
    simpri $p |- ps $=
      ( wa simpr ax-mp ) ABDBCABEF $.
      $( [15-Jun-1994] $)
  $}

  ${
    simprd.1 $e |- ( ph -> ( ps /\ ch ) ) $.
    $( Deduction eliminating a conjunct.  (The proof was shortened by Wolf
       Lammen, 3-Oct-2013.) $)
    simprd $p |- ( ph -> ch ) $=
      ( ancomd simpld ) ACBABCDEF $.
      $( [3-Oct-2013] $) $( [5-Aug-1993] $)
  $}

  ${
    simprbi.1 $e |- ( ph <-> ( ps /\ ch ) ) $.
    $( Deduction eliminating a conjunct. $)
    simprbi $p |- ( ph -> ch ) $=
      ( wa biimpi simprd ) ABCABCEDFG $.
      $( [27-May-1998] $)
  $}

  ${
    adantr.1 $e |- ( ph -> ps ) $.
    $( Inference adding a conjunct to the right of an antecedent. $)
    adantr $p |- ( ( ph /\ ch ) -> ps ) $=
      ( a1d imp ) ACBABCDEF $.
      $( [30-Aug-1993] $)
  $}

  ${
    adantl.1 $e |- ( ph -> ps ) $.
    $( Inference adding a conjunct to the left of an antecedent.  (The proof
       was shortened by Wolf Lammen, 23-Nov-2012.) $)
    adantl $p |- ( ( ch /\ ph ) -> ps ) $=
      ( adantr ancoms ) ACBABCDEF $.
      $( [23-Nov-2012] $) $( [30-Aug-1993] $)
  $}

  ${
    adantld.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Deduction adding a conjunct to the left of an antecedent.  (The proof
       was shortened by Wolf Lammen, 20-Dec-2012.) $)
    adantld $p |- ( ph -> ( ( th /\ ps ) -> ch ) ) $=
      ( wa simpr syl5 ) DBFBACDBGEH $.
      $( [20-Dec-2012] $) $( [4-May-1994] $)
  $}

  ${
    adantrd.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Deduction adding a conjunct to the right of an antecedent. $)
    adantrd $p |- ( ph -> ( ( ps /\ th ) -> ch ) ) $=
      ( wa simpl syl5 ) BDFBACBDGEH $.
      $( [4-May-1994] $)
  $}

  ${
    mpan9.1 $e |- ( ph -> ps ) $.
    mpan9.2 $e |- ( ch -> ( ps -> th ) ) $.
    $( Modus ponens conjoining dissimilar antecedents.  (The proof was
       shortened by Andrew Salmon, 7-May-2011.) $)
    mpan9 $p |- ( ( ph /\ ch ) -> th ) $=
      ( syl5 impcom ) CADABCDEFGH $.
      $( [12-May-2011] $) $( [1-Feb-2008] $)
  $}

  ${
    syldan.1 $e |- ( ( ph /\ ps ) -> ch ) $.
    syldan.2 $e |- ( ( ph /\ ch ) -> th ) $.
    $( A syllogism deduction with conjoined antecents.  (The proof was
       shortened by Wolf Lammen, 6-Apr-2013.) $)
    syldan $p |- ( ( ph /\ ps ) -> th ) $=
      ( wa expcom adantrd mpcom ) CABGDECADBACDFHIJ $.
      $( [6-Apr-2013] $) $( [24-Feb-2005] $)
  $}

  ${
    sylan.1 $e |- ( ph -> ps ) $.
    sylan.2 $e |- ( ( ps /\ ch ) -> th ) $.
    $( A syllogism inference.  (The proof was shortened by Wolf Lammen,
       22-Nov-2012.) $)
    sylan $p |- ( ( ph /\ ch ) -> th ) $=
      ( expcom mpan9 ) ABCDEBCDFGH $.
      $( [22-Nov-2012] $) $( [21-Apr-1994] $)
  $}

  ${
    sylanb.1 $e |- ( ph <-> ps ) $.
    sylanb.2 $e |- ( ( ps /\ ch ) -> th ) $.
    $( A syllogism inference. $)
    sylanb $p |- ( ( ph /\ ch ) -> th ) $=
      ( biimpi sylan ) ABCDABEGFH $.
      $( [18-May-1994] $)
  $}

  ${
    sylanbr.1 $e |- ( ps <-> ph ) $.
    sylanbr.2 $e |- ( ( ps /\ ch ) -> th ) $.
    $( A syllogism inference. $)
    sylanbr $p |- ( ( ph /\ ch ) -> th ) $=
      ( biimpri sylan ) ABCDBAEGFH $.
      $( [18-May-1994] $)
  $}

  ${
    sylan2.1 $e |- ( ph -> ch ) $.
    sylan2.2 $e |- ( ( ps /\ ch ) -> th ) $.
    $( A syllogism inference.  (The proof was shortened by Wolf Lammen,
       22-Nov-2012.) $)
    sylan2 $p |- ( ( ps /\ ph ) -> th ) $=
      ( adantl syldan ) BACDACBEGFH $.
      $( [22-Nov-2012] $) $( [21-Apr-1994] $)
  $}

  ${
    sylan2b.1 $e |- ( ph <-> ch ) $.
    sylan2b.2 $e |- ( ( ps /\ ch ) -> th ) $.
    $( A syllogism inference. $)
    sylan2b $p |- ( ( ps /\ ph ) -> th ) $=
      ( biimpi sylan2 ) ABCDACEGFH $.
      $( [21-Apr-1994] $)
  $}

  ${
    sylan2br.1 $e |- ( ch <-> ph ) $.
    sylan2br.2 $e |- ( ( ps /\ ch ) -> th ) $.
    $( A syllogism inference. $)
    sylan2br $p |- ( ( ps /\ ph ) -> th ) $=
      ( biimpri sylan2 ) ABCDCAEGFH $.
      $( [21-Apr-1994] $)
  $}

  ${
    syl2an.1 $e |- ( ph -> ps ) $.
    syl2an.2 $e |- ( ta -> ch ) $.
    syl2an.3 $e |- ( ( ps /\ ch ) -> th ) $.
    $( A double syllogism inference. $)
    syl2an $p |- ( ( ph /\ ta ) -> th ) $=
      ( sylan sylan2 ) EACDGABCDFHIJ $.
      $( [31-Jan-1997] $)

    $( A double syllogism inference. $)
    syl2anr $p |- ( ( ta /\ ph ) -> th ) $=
      ( syl2an ancoms ) AEDABCDEFGHIJ $.
      $( [17-Sep-2013] $)
  $}

  ${
    syl2anb.1 $e |- ( ph <-> ps ) $.
    syl2anb.2 $e |- ( ta <-> ch ) $.
    syl2anb.3 $e |- ( ( ps /\ ch ) -> th ) $.
    $( A double syllogism inference. $)
    syl2anb $p |- ( ( ph /\ ta ) -> th ) $=
      ( sylanb sylan2b ) EACDGABCDFHIJ $.
      $( [29-Jul-1999] $)
  $}

  ${
    syl2anbr.1 $e |- ( ps <-> ph ) $.
    syl2anbr.2 $e |- ( ch <-> ta ) $.
    syl2anbr.3 $e |- ( ( ps /\ ch ) -> th ) $.
    $( A double syllogism inference. $)
    syl2anbr $p |- ( ( ph /\ ta ) -> th ) $=
      ( sylanbr sylan2br ) EACDGABCDFHIJ $.
      $( [29-Jul-1999] $)
  $}

  ${
    syland.1 $e |- ( ph -> ( ps -> ch ) ) $.
    syland.2 $e |- ( ph -> ( ( ch /\ th ) -> ta ) ) $.
    $( A syllogism deduction. $)
    syland $p |- ( ph -> ( ( ps /\ th ) -> ta ) ) $=
      ( wi exp3a syld imp3a ) ABDEABCDEHFACDEGIJK $.
      $( [15-Dec-2004] $)
  $}

  ${
    sylan2d.1 $e |- ( ph -> ( ps -> ch ) ) $.
    sylan2d.2 $e |- ( ph -> ( ( th /\ ch ) -> ta ) ) $.
    $( A syllogism deduction. $)
    sylan2d $p |- ( ph -> ( ( th /\ ps ) -> ta ) ) $=
      ( ancomsd syland ) ABDEABCDEFADCEGHIH $.
      $( [15-Dec-2004] $)
  $}

  ${
    syl2and.1 $e |- ( ph -> ( ps -> ch ) ) $.
    syl2and.2 $e |- ( ph -> ( th -> ta ) ) $.
    syl2and.3 $e |- ( ph -> ( ( ch /\ ta ) -> et ) ) $.
    $( A syllogism deduction. $)
    syl2and $p |- ( ph -> ( ( ps /\ th ) -> et ) ) $=
      ( sylan2d syland ) ABCDFGADECFHIJK $.
      $( [15-Dec-2004] $)
  $}

  ${
    biimpa.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Inference from a logical equivalence. $)
    biimpa $p |- ( ( ph /\ ps ) -> ch ) $=
      ( biimpd imp ) ABCABCDEF $.
      $( [3-May-1994] $)

    $( Inference from a logical equivalence. $)
    biimpar $p |- ( ( ph /\ ch ) -> ps ) $=
      ( biimprd imp ) ACBABCDEF $.
      $( [3-May-1994] $)

    $( Inference from a logical equivalence. $)
    biimpac $p |- ( ( ps /\ ph ) -> ch ) $=
      ( biimpcd imp ) BACABCDEF $.
      $( [3-May-1994] $)

    $( Inference from a logical equivalence. $)
    biimparc $p |- ( ( ch /\ ph ) -> ps ) $=
      ( biimprcd imp ) CABABCDEF $.
      $( [3-May-1994] $)
  $}

  $( Negated conjunction in terms of disjunction (DeMorgan's law).  Theorem
     *4.51 of [WhiteheadRussell] p. 120.  (The proof was shortened by Andrew
     Salmon, 13-May-2011.) $)
  ianor $p |- ( -. ( ph /\ ps ) <-> ( -. ph \/ -. ps ) ) $=
    ( wa wn wi wo imnan pm4.62 bitr3i ) ABCDABDZEADJFABGABHI $.
    $( [3-Nov-2012] $) $( [5-Aug-1993] $)

  $( Conjunction in terms of disjunction (DeMorgan's law).  Theorem *4.5 of
     [WhiteheadRussell] p. 120.  (The proof was shortened by Wolf Lammen,
     3-Nov-2012.) $)
  anor $p |- ( ( ph /\ ps ) <-> -. ( -. ph \/ -. ps ) ) $=
    ( wn wo wa ianor bicomi con2bii ) ACBCDZABEZJCIABFGH $.
    $( [3-Nov-2012] $) $( [5-Aug-1993] $)

  $( Negated disjunction in terms of conjunction (DeMorgan's law).  Compare
     Theorem *4.56 of [WhiteheadRussell] p. 120.  (The proof was shortened by
     Andrew Salmon, 7-May-2011.) $)
  ioran $p |- ( -. ( ph \/ ps ) <-> ( -. ph /\ -. ps ) ) $=
    ( wn wi wa wo pm4.61 pm4.64 xchnxbi ) ACZBDJBCEABFJBGABHI $.
    $( [28-Sep-2014] $) $( [5-Aug-1993] $)

  $( Obsolete proof of ~ ioran as of 28-Sep-2014. $)
  ioranOLD $p |- ( -. ( ph \/ ps ) <-> ( -. ph /\ -. ps ) ) $=
    ( wo wn wi wa df-or notbii annim bitr4i ) ABCZDADZBEZDLBDFKMABGHLBIJ $.
    $( [12-May-2011] $) $( [5-Aug-1993] $)

  $( Theorem *4.52 of [WhiteheadRussell] p. 120.  (The proof was shortened by
     Wolf Lammen, 5-Nov-2012.) $)
  pm4.52 $p |- ( ( ph /\ -. ps ) <-> -. ( -. ph \/ ps ) ) $=
    ( wn wa wi wo annim imor xchbinx ) ABCDABEACBFABGABHI $.
    $( [5-Nov-2012] $) $( [3-Jan-2005] $)

  $( Theorem *4.53 of [WhiteheadRussell] p. 120. $)
  pm4.53 $p |- ( -. ( ph /\ -. ps ) <-> ( -. ph \/ ps ) ) $=
    ( wn wo wa pm4.52 con2bii bicomi ) ACBDZABCEZCJIABFGH $.
    $( [3-Jan-2005] $)

  $( Theorem *4.54 of [WhiteheadRussell] p. 120.  (The proof was shortened by
     Wolf Lammen, 5-Nov-2012.) $)
  pm4.54 $p |- ( ( -. ph /\ ps ) <-> -. ( ph \/ -. ps ) ) $=
    ( wn wa wi wo df-an pm4.66 xchbinx ) ACZBDJBCZEAKFJBGABHI $.
    $( [28-Sep-2014] $) $( [3-Jan-2005] $)

  $( Obsolete proof of ~ pm4.54 as of 28-Sep-2014. $)
  pm4.54OLD $p |- ( ( -. ph /\ ps ) <-> -. ( ph \/ -. ps ) ) $=
    ( wn wa wi wo pm4.67 pm4.66 notbii bitr3i ) ACZBDKBCZEZCALFZCABGMNABHIJ $.
    $( [5-Nov-2012] $) $( [3-Jan-2005] $)

  $( Theorem *4.55 of [WhiteheadRussell] p. 120. $)
  pm4.55 $p |- ( -. ( -. ph /\ ps ) <-> ( ph \/ -. ps ) ) $=
    ( wn wo wa pm4.54 con2bii bicomi ) ABCDZACBEZCJIABFGH $.
    $( [3-Jan-2005] $)

  $( Theorem *4.56 of [WhiteheadRussell] p. 120. $)
  pm4.56 $p |- ( ( -. ph /\ -. ps ) <-> -. ( ph \/ ps ) ) $=
    ( wo wn wa ioran bicomi ) ABCDADBDEABFG $.
    $( [3-Jan-2005] $)

  $( Disjunction in terms of conjunction (DeMorgan's law).  Compare Theorem
     *4.57 of [WhiteheadRussell] p. 120.  (The proof was shortened by Andrew
     Salmon, 7-May-2011.) $)
  oran $p |- ( ( ph \/ ps ) <-> -. ( -. ph /\ -. ps ) ) $=
    ( wn wa wo pm4.56 con2bii ) ACBCDABEABFG $.
    $( [12-May-2011] $) $( [5-Aug-1993] $)

  $( Theorem *4.57 of [WhiteheadRussell] p. 120. $)
  pm4.57 $p |- ( -. ( -. ph /\ -. ps ) <-> ( ph \/ ps ) ) $=
    ( wo wn wa oran bicomi ) ABCADBDEDABFG $.
    $( [3-Jan-2005] $)

  $( Theorem *3.1 of [WhiteheadRussell] p. 111. $)
  pm3.1 $p |- ( ( ph /\ ps ) -> -. ( -. ph \/ -. ps ) ) $=
    ( wa wn wo anor biimpi ) ABCADBDEDABFG $.
    $( [3-Jan-2005] $)

  $( Theorem *3.11 of [WhiteheadRussell] p. 111. $)
  pm3.11 $p |- ( -. ( -. ph \/ -. ps ) -> ( ph /\ ps ) ) $=
    ( wa wn wo anor biimpri ) ABCADBDEDABFG $.
    $( [3-Jan-2005] $)

  $( Theorem *3.12 of [WhiteheadRussell] p. 111. $)
  pm3.12 $p |- ( ( -. ph \/ -. ps ) \/ ( ph /\ ps ) ) $=
    ( wn wo wa pm3.11 orri ) ACBCDABEABFG $.
    $( [3-Jan-2005] $)

  $( Theorem *3.13 of [WhiteheadRussell] p. 111. $)
  pm3.13 $p |- ( -. ( ph /\ ps ) -> ( -. ph \/ -. ps ) ) $=
    ( wn wo wa pm3.11 con1i ) ACBCDABEABFG $.
    $( [3-Jan-2005] $)

  $( Theorem *3.14 of [WhiteheadRussell] p. 111. $)
  pm3.14 $p |- ( ( -. ph \/ -. ps ) -> -. ( ph /\ ps ) ) $=
    ( wa wn wo pm3.1 con2i ) ABCADBDEABFG $.
    $( [3-Jan-2005] $)

  $( Introduction of antecedent as conjunct.  Theorem *4.73 of
     [WhiteheadRussell] p. 121. $)
  iba $p |- ( ph -> ( ps <-> ( ps /\ ph ) ) ) $=
    ( wa pm3.21 simpl impbid1 ) ABBACABDBAEF $.
    $( [24-Mar-2013] $) $( [30-Mar-1994] $)

  $( Introduction of antecedent as conjunct. $)
  ibar $p |- ( ph -> ( ps <-> ( ph /\ ps ) ) ) $=
    ( wa pm3.2 simpr impbid1 ) ABABCABDABEF $.
    $( [24-Mar-2013] $) $( [5-Dec-1995] $)
  ${
    biantru.1 $e |- ph $.
    $( A wff is equivalent to its conjunction with truth. $)
    biantru $p |- ( ps <-> ( ps /\ ph ) ) $=
      ( wa wb iba ax-mp ) ABBADECABFG $.
      $( [5-Aug-1993] $)
  $}

  ${
    biantrur.1 $e |- ph $.
    $( A wff is equivalent to its conjunction with truth. $)
    biantrur $p |- ( ps <-> ( ph /\ ps ) ) $=
      ( wa wb ibar ax-mp ) ABABDECABFG $.
      $( [3-Aug-1994] $)
  $}

  ${
    biantrud.1 $e |- ( ph -> ps ) $.
    $( A wff is equivalent to its conjunction with truth.  (The proof was
       shortened by Wolf Lammen, 23-Oct-2013.) $)
    biantrud $p |- ( ph -> ( ch <-> ( ch /\ ps ) ) ) $=
      ( wa wb iba syl ) ABCCBEFDBCGH $.
      $( [23-Oct-2013] $) $( [2-Aug-1994] $)

    $( A wff is equivalent to its conjunction with truth.  (The proof was
       shortened by Andrew Salmon, 7-May-2011.) $)
    biantrurd $p |- ( ph -> ( ch <-> ( ps /\ ch ) ) ) $=
      ( wa wb ibar syl ) ABCBCEFDBCGH $.
      $( [12-May-2011] $) $( [1-May-1995] $)
  $}

  ${
    jaao.1 $e |- ( ph -> ( ps -> ch ) ) $.
    jaao.2 $e |- ( th -> ( ta -> ch ) ) $.
    $( Inference conjoining and disjoining the antecedents of two
       implications. $)
    jaao $p |- ( ( ph /\ th ) -> ( ( ps \/ ta ) -> ch ) ) $=
      ( wa wi adantr adantl jaod ) ADHBCEABCIDFJDECIAGKL $.
      $( [30-Sep-1999] $)

    $( Inference disjoining and conjoining the antecedents of two
       implications.  (Contributed by Stefan Allan, 1-Nov-2008.) $)
    jaoa $p |- ( ( ph \/ th ) -> ( ( ps /\ ta ) -> ch ) ) $=
      ( wa wi adantrd adantld jaoi ) ABEHCIDABCEFJDECBGKL $.
      $( [1-Nov-2008] $)
  $}

  $( Theorem *3.44 of [WhiteheadRussell] p. 113.  (The proof was shortened by
     Wolf Lammen, 3-Oct-2013.) $)
  pm3.44 $p |- ( ( ( ps -> ph ) /\ ( ch -> ph ) ) ->
                ( ( ps \/ ch ) -> ph ) ) $=
    ( wi id jaao ) BADZBACADZCGEHEF $.
    $( [3-Oct-2013] $) $( [3-Jan-2005] $)

  $( Disjunction of antecedents.  Compare Theorem *3.44 of [WhiteheadRussell]
     p. 113.  (The proof was shortened by Wolf Lammen, 4-Apr-2013.) $)
  jao $p |- ( ( ph -> ps ) -> ( ( ch -> ps ) -> ( ( ph \/ ch ) -> ps ) ) ) $=
    ( wi wo pm3.44 ex ) ABDCBDACEBDBACFG $.
    $( [4-Apr-2013] $) $( [5-Apr-1994] $)

  $( Axiom *1.2 (Taut) of [WhiteheadRussell] p. 96. $)
  pm1.2 $p |- ( ( ph \/ ph ) -> ph ) $=
    ( id jaoi ) AAAABZDC $.
    $( [10-Mar-2013] $) $( [3-Jan-2005] $)

  $( Idempotent law for disjunction.  Theorem *4.25 of [WhiteheadRussell]
     p. 117.  (The proof was shortened by Andrew Salmon, 16-Apr-2011.)  (The
     proof was shortened by Wolf Lammen, 10-Mar-2013.) $)
  oridm $p |- ( ( ph \/ ph ) <-> ph ) $=
    ( wo pm1.2 pm2.07 impbii ) AABAACADE $.
    $( [10-Mar-2013] $) $( [5-Aug-1993] $)

  $( Theorem *4.25 of [WhiteheadRussell] p. 117. $)
  pm4.25 $p |- ( ph <-> ( ph \/ ph ) ) $=
    ( wo oridm bicomi ) AABAACD $.
    $( [3-Jan-2005] $)

  ${
    orim12i.1 $e |- ( ph -> ps ) $.
    orim12i.2 $e |- ( ch -> th ) $.
    $( Disjoin antecedents and consequents of two premises.  (The proof was
       shortened by Wolf Lammen, 25-Jul-2012.) $)
    orim12i $p |- ( ( ph \/ ch ) -> ( ps \/ th ) ) $=
      ( wo orcd olcd jaoi ) ABDGCABDEHCDBFIJ $.
      $( [25-Jul-2012] $) $( [6-Jun-1994] $)
  $}

  ${
    orim1i.1 $e |- ( ph -> ps ) $.
    $( Introduce disjunct to both sides of an implication. $)
    orim1i $p |- ( ( ph \/ ch ) -> ( ps \/ ch ) ) $=
      ( id orim12i ) ABCCDCEF $.
      $( [6-Jun-1994] $)

    $( Introduce disjunct to both sides of an implication. $)
    orim2i $p |- ( ( ch \/ ph ) -> ( ch \/ ps ) ) $=
      ( id orim12i ) CCABCEDF $.
      $( [6-Jun-1994] $)
  $}

  ${
    orbi2i.1 $e |- ( ph <-> ps ) $.
    $( Inference adding a left disjunct to both sides of a logical
       equivalence.  (The proof was shortened by Wolf Lammen, 12-Dec-2012.) $)
    orbi2i $p |- ( ( ch \/ ph ) <-> ( ch \/ ps ) ) $=
      ( wo biimpi orim2i biimpri impbii ) CAECBEABCABDFGBACABDHGI $.
      $( [12-Dec-2012] $) $( [5-Aug-1993] $)

    $( Inference adding a right disjunct to both sides of a logical
       equivalence. $)
    orbi1i $p |- ( ( ph \/ ch ) <-> ( ps \/ ch ) ) $=
      ( wo orcom orbi2i 3bitri ) ACECAECBEBCEACFABCDGCBFH $.
      $( [5-Aug-1993] $)
  $}

  ${
    orbi12i.1 $e |- ( ph <-> ps ) $.
    orbi12i.2 $e |- ( ch <-> th ) $.
    $( Infer the disjunction of two equivalences. $)
    orbi12i $p |- ( ( ph \/ ch ) <-> ( ps \/ th ) ) $=
      ( wo orbi2i orbi1i bitri ) ACGADGBDGCDAFHABDEIJ $.
      $( [5-Aug-1993] $)
  $}

  $( Axiom *1.5 (Assoc) of [WhiteheadRussell] p. 96. $)
  pm1.5 $p |- ( ( ph \/ ( ps \/ ch ) ) -> ( ps \/ ( ph \/ ch ) ) ) $=
    ( wo orc olcd olc orim2i jaoi ) ABACDZDBCDAJBACEFCJBCAGHI $.
    $( [3-Jan-2005] $)

  $( Swap two disjuncts.  (The proof was shortened by Wolf Lammen,
     14-Nov-2012.) $)
  or12 $p |- ( ( ph \/ ( ps \/ ch ) ) <-> ( ps \/ ( ph \/ ch ) ) ) $=
    ( wo pm1.5 impbii ) ABCDDBACDDABCEBACEF $.
    $( [14-Nov-2012] $) $( [5-Aug-1993] $)

  $( Associative law for disjunction.  Theorem *4.33 of [WhiteheadRussell]
     p. 118.  (The proof was shortened by Andrew Salmon, 26-Jun-2011.) $)
  orass $p |- ( ( ( ph \/ ps ) \/ ch ) <-> ( ph \/ ( ps \/ ch ) ) ) $=
    ( wo orcom or12 orbi2i 3bitri ) ABDZCDCIDACBDZDABCDZDICECABFJKACBEGH $.
    $( [26-Jun-2011] $) $( [5-Aug-1993] $)

  $( Theorem *2.31 of [WhiteheadRussell] p. 104. $)
  pm2.31 $p |- ( ( ph \/ ( ps \/ ch ) ) -> ( ( ph \/ ps ) \/ ch ) ) $=
    ( wo orass biimpri ) ABDCDABCDDABCEF $.
    $( [3-Jan-2005] $)

  $( Theorem *2.32 of [WhiteheadRussell] p. 105. $)
  pm2.32 $p |- ( ( ( ph \/ ps ) \/ ch ) -> ( ph \/ ( ps \/ ch ) ) ) $=
    ( wo orass biimpi ) ABDCDABCDDABCEF $.
    $( [3-Jan-2005] $)

  $( A rearrangement of disjuncts.  (The proof was shortened by Andrew Salmon,
     26-Jun-2011.) $)
  or32 $p |- ( ( ( ph \/ ps ) \/ ch ) <-> ( ( ph \/ ch ) \/ ps ) ) $=
    ( wo orass or12 orcom 3bitri ) ABDCDABCDDBACDZDIBDABCEABCFBIGH $.
    $( [26-Jun-2011] $) $( [18-Oct-1995] $)

  $( Rearrangement of 4 disjuncts. $)
  or4 $p |- ( ( ( ph \/ ps ) \/ ( ch \/ th ) ) <->
                ( ( ph \/ ch ) \/ ( ps \/ th ) ) ) $=
    ( wo or12 orbi2i orass 3bitr4i ) ABCDEZEZEACBDEZEZEABEJEACELEKMABCDFGABJHAC
    LHI $.
    $( [12-Aug-1994] $)

  $( Rearrangement of 4 disjuncts. $)
  or42 $p |- ( ( ( ph \/ ps ) \/ ( ch \/ th ) ) <->
                 ( ( ph \/ ch ) \/ ( th \/ ps ) ) ) $=
    ( wo or4 orcom orbi2i bitri ) ABECDEEACEZBDEZEJDBEZEABCDFKLJBDGHI $.
    $( [10-Jan-2005] $)

  $( Distribution of disjunction over disjunction. $)
  orordi $p |- ( ( ph \/ ( ps \/ ch ) ) <->
               ( ( ph \/ ps ) \/ ( ph \/ ch ) ) ) $=
    ( wo oridm orbi1i or4 bitr3i ) ABCDZDAADZIDABDACDDJAIAEFAABCGH $.
    $( [25-Feb-1995] $)

  $( Distribution of disjunction over disjunction. $)
  orordir $p |- ( ( ( ph \/ ps ) \/ ch ) <->
               ( ( ph \/ ch ) \/ ( ps \/ ch ) ) ) $=
    ( wo oridm orbi2i or4 bitr3i ) ABDZCDICCDZDACDBCDDJCICEFABCCGH $.
    $( [25-Feb-1995] $)

  ${
    jca.1 $e |- ( ph -> ps ) $.
    jca.2 $e |- ( ph -> ch ) $.
    $( Deduce conjunction of the consequents of two implications ("join
       consequents with 'and'").  (The proof was shortened by Wolf Lammen,
       25-Oct-2012.) $)
    jca $p |- ( ph -> ( ps /\ ch ) ) $=
      ( wa pm3.2 sylc ) ABCBCFDEBCGH $.
      $( [25-Oct-2012] $) $( [5-Aug-1993] $)
  $}

  ${
    jcad.1 $e |- ( ph -> ( ps -> ch ) ) $.
    jcad.2 $e |- ( ph -> ( ps -> th ) ) $.
    $( Deduction conjoining the consequents of two implications.  (The proof
       was shortened by Wolf Lammen, 23-Jul-2013.) $)
    jcad $p |- ( ph -> ( ps -> ( ch /\ th ) ) ) $=
      ( wa pm3.2 syl6c ) ABCDCDGEFCDHI $.
      $( [23-Jul-2013] $) $( [5-Aug-1993] $)
  $}

  ${
    jca31.1 $e |- ( ph -> ps ) $.
    jca31.2 $e |- ( ph -> ch ) $.
    jca31.3 $e |- ( ph -> th ) $.
    $( Join three consequents.  (Contributed by Jeff Hankins, 1-Aug-2009.) $)
    jca31 $p |- ( ph -> ( ( ps /\ ch ) /\ th ) ) $=
      ( wa jca ) ABCHDABCEFIGI $.
      $( [1-Aug-2009] $)

    $( Join three consequents.  (Contributed by FL, 1-Aug-2009.) $)
    jca32 $p |- ( ph -> ( ps /\ ( ch /\ th ) ) ) $=
      ( wa jca ) ABCDHEACDFGII $.
      $( [1-Aug-2009] $)
  $}

  ${
    jcai.1 $e |- ( ph -> ps ) $.
    jcai.2 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Deduction replacing implication with conjunction. $)
    jcai $p |- ( ph -> ( ps /\ ch ) ) $=
      ( mpd jca ) ABCDABCDEFG $.
      $( [5-Aug-1993] $)
  $}

  ${
    jctil.1 $e |- ( ph -> ps ) $.
    jctil.2 $e |- ch $.
    $( Inference conjoining a theorem to left of consequent in an
       implication. $)
    jctil $p |- ( ph -> ( ch /\ ps ) ) $=
      ( a1i jca ) ACBCAEFDG $.
      $( [31-Dec-1993] $)

    $( Inference conjoining a theorem to right of consequent in an
       implication. $)
    jctir $p |- ( ph -> ( ps /\ ch ) ) $=
      ( a1i jca ) ABCDCAEFG $.
      $( [31-Dec-1993] $)
  $}

  ${
    jctl.1 $e |- ps $.
    $( Inference conjoining a theorem to the left of a consequent.  (The proof
       was shortened by Wolf Lammen, 24-Oct-2012.) $)
    jctl $p |- ( ph -> ( ps /\ ph ) ) $=
      ( id jctil ) AABADCE $.
      $( [25-Oct-2012] $) $( [31-Dec-1993] $)

    $( Inference conjoining a theorem to the right of a consequent.  (The proof
       was shortened by Wolf Lammen, 24-Oct-2012.) $)
    jctr $p |- ( ph -> ( ph /\ ps ) ) $=
      ( id jctir ) AABADCE $.
      $( [25-Oct-2012] $) $( [18-Aug-1993] $)
  $}

  ${
    jctild.1 $e |- ( ph -> ( ps -> ch ) ) $.
    jctild.2 $e |- ( ph -> th ) $.
    $( Deduction conjoining a theorem to left of consequent in an
       implication. $)
    jctild $p |- ( ph -> ( ps -> ( th /\ ch ) ) ) $=
      ( a1d jcad ) ABDCADBFGEH $.
      $( [21-Apr-2005] $)
  $}

  ${
    jctird.1 $e |- ( ph -> ( ps -> ch ) ) $.
    jctird.2 $e |- ( ph -> th ) $.
    $( Deduction conjoining a theorem to right of consequent in an
       implication. $)
    jctird $p |- ( ph -> ( ps -> ( ch /\ th ) ) ) $=
      ( a1d jcad ) ABCDEADBFGH $.
      $( [21-Apr-2005] $)
  $}

  $( Conjoin antecedent to left of consequent. $)
  ancl $p |- ( ( ph -> ps ) -> ( ph -> ( ph /\ ps ) ) ) $=
    ( wa pm3.2 a2i ) ABABCABDE $.
    $( [15-Aug-1994] $)

  $( Conjoin antecedent to left of consequent.  Theorem *4.7 of
     [WhiteheadRussell] p. 120.  (The proof was shortened by Wolf Lammen,
     24-Mar-2013.) $)
  anclb $p |- ( ( ph -> ps ) <-> ( ph -> ( ph /\ ps ) ) ) $=
    ( wa ibar pm5.74i ) ABABCABDE $.
    $( [24-Mar-2013] $) $( [25-Jul-1999] $)

  $( Theorem *5.42 of [WhiteheadRussell] p. 125. $)
  pm5.42 $p |- ( ( ph -> ( ps -> ch ) ) <->
                ( ph -> ( ps -> ( ph /\ ch ) ) ) ) $=
    ( wi wa ibar imbi2d pm5.74i ) ABCDBACEZDACIBACFGH $.
    $( [3-Jan-2005] $)

  $( Conjoin antecedent to right of consequent. $)
  ancr $p |- ( ( ph -> ps ) -> ( ph -> ( ps /\ ph ) ) ) $=
    ( wa pm3.21 a2i ) ABBACABDE $.
    $( [15-Aug-1994] $)

  $( Conjoin antecedent to right of consequent.  (The proof was shortened by
     Wolf Lammen, 24-Mar-2013.) $)
  ancrb $p |- ( ( ph -> ps ) <-> ( ph -> ( ps /\ ph ) ) ) $=
    ( wa iba pm5.74i ) ABBACABDE $.
    $( [24-Mar-2013] $) $( [25-Jul-1999] $)

  ${
    ancli.1 $e |- ( ph -> ps ) $.
    $( Deduction conjoining antecedent to left of consequent. $)
    ancli $p |- ( ph -> ( ph /\ ps ) ) $=
      ( id jca ) AABADCE $.
      $( [12-Aug-1993] $)
  $}

  ${
    ancri.1 $e |- ( ph -> ps ) $.
    $( Deduction conjoining antecedent to right of consequent. $)
    ancri $p |- ( ph -> ( ps /\ ph ) ) $=
      ( id jca ) ABACADE $.
      $( [15-Aug-1994] $)
  $}

  ${
    ancld.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Deduction conjoining antecedent to left of consequent in nested
       implication.  (The proof was shortened by Wolf Lammen, 1-Nov-2012.) $)
    ancld $p |- ( ph -> ( ps -> ( ps /\ ch ) ) ) $=
      ( idd jcad ) ABBCABEDF $.
      $( [1-Nov-2012] $) $( [15-Aug-1994] $)
  $}

  ${
    ancrd.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Deduction conjoining antecedent to right of consequent in nested
       implication.  (The proof was shortened by Wolf Lammen, 1-Nov-2012.) $)
    ancrd $p |- ( ph -> ( ps -> ( ch /\ ps ) ) ) $=
      ( idd jcad ) ABCBDABEF $.
      $( [1-Nov-2012] $) $( [15-Aug-1994] $)
  $}

  $( Conjoin antecedent to left of consequent in nested implication.  (The
     proof was shortened by Wolf Lammen, 14-Jul-2013.) $)
  anc2l $p |- ( ( ph -> ( ps -> ch ) ) -> ( ph -> ( ps -> ( ph /\ ch ) ) ) ) $=
    ( wi wa pm5.42 biimpi ) ABCDDABACEDDABCFG $.
    $( [14-Jul-2013] $) $( [10-Aug-1994] $)

  $( Conjoin antecedent to right of consequent in nested implication. $)
  anc2r $p |- ( ( ph -> ( ps -> ch ) ) -> ( ph -> ( ps -> ( ch /\ ph ) ) ) ) $=
    ( wi wa pm3.21 imim2d a2i ) ABCDBCAEZDACIBACFGH $.
    $( [15-Aug-1994] $)

  ${
    anc2li.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Deduction conjoining antecedent to left of consequent in nested
       implication.  (The proof was shortened by Wolf Lammen, 7-Dec-2012.) $)
    anc2li $p |- ( ph -> ( ps -> ( ph /\ ch ) ) ) $=
      ( id jctild ) ABCADAEF $.
      $( [7-Dec-2012] $) $( [10-Aug-1994] $)
  $}

  ${
    anc2ri.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Deduction conjoining antecedent to right of consequent in nested
       implication.  (The proof was shortened by Wolf Lammen, 7-Dec-2012.) $)
    anc2ri $p |- ( ph -> ( ps -> ( ch /\ ph ) ) ) $=
      ( id jctird ) ABCADAEF $.
      $( [7-Dec-2012] $) $( [15-Aug-1994] $)
  $}

  $( Theorem *3.41 of [WhiteheadRussell] p. 113. $)
  pm3.41 $p |- ( ( ph -> ch ) -> ( ( ph /\ ps ) -> ch ) ) $=
    ( wa simpl imim1i ) ABDACABEF $.
    $( [3-Jan-2005] $)

  $( Theorem *3.42 of [WhiteheadRussell] p. 113. $)
  pm3.42 $p |- ( ( ps -> ch ) -> ( ( ph /\ ps ) -> ch ) ) $=
    ( wa simpr imim1i ) ABDBCABEF $.
    $( [3-Jan-2005] $)

  $( Conjunction implies implication.  Theorem *3.4 of [WhiteheadRussell]
     p. 113. $)
  pm3.4 $p |- ( ( ph /\ ps ) -> ( ph -> ps ) ) $=
    ( wa simpr a1d ) ABCBAABDE $.
    $( [31-Jul-1995] $)

  $( Conjunction with implication.  Compare Theorem *4.45 of [WhiteheadRussell]
     p. 119. $)
  pm4.45im $p |- ( ph <-> ( ph /\ ( ps -> ph ) ) ) $=
    ( wi wa ax-1 ancli simpl impbii ) AABACZDAIABEFAIGH $.
    $( [17-May-1998] $)

  ${
    anim12d.1 $e |- ( ph -> ( ps -> ch ) ) $.
    anim12d.2 $e |- ( ph -> ( th -> ta ) ) $.
    $( Conjoin antecedents and consequents in a deduction.  (The proof was
       shortened by Wolf Lammen, 18-Dec-2013.) $)
    anim12d $p |- ( ph -> ( ( ps /\ th ) -> ( ch /\ ta ) ) ) $=
      ( wa idd syl2and ) ABCDECEHZFGAKIJ $.
      $( [18-Dec-2013] $) $( [3-Apr-1994] $)
  $}

  ${
    anim1d.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Add a conjunct to right of antecedent and consequent in a deduction. $)
    anim1d $p |- ( ph -> ( ( ps /\ th ) -> ( ch /\ th ) ) ) $=
      ( idd anim12d ) ABCDDEADFG $.
      $( [3-Apr-1994] $)

    $( Add a conjunct to left of antecedent and consequent in a deduction. $)
    anim2d $p |- ( ph -> ( ( th /\ ps ) -> ( th /\ ch ) ) ) $=
      ( idd anim12d ) ADDBCADFEG $.
      $( [5-Aug-1993] $)
  $}

  ${
    anim12i.1 $e |- ( ph -> ps ) $.
    anim12i.2 $e |- ( ch -> th ) $.
    $( Conjoin antecedents and consequents of two premises.  (The proof was
       shortened by Wolf Lammen, 14-Dec-2013.) $)
    anim12i $p |- ( ( ph /\ ch ) -> ( ps /\ th ) ) $=
      ( wa id syl2an ) ABDBDGZCEFJHI $.
      $( [14-Dec-2013] $) $( [5-Aug-1993] $)
  $}

  ${
    anim1i.1 $e |- ( ph -> ps ) $.
    $( Introduce conjunct to both sides of an implication. $)
    anim1i $p |- ( ( ph /\ ch ) -> ( ps /\ ch ) ) $=
      ( id anim12i ) ABCCDCEF $.
      $( [5-Aug-1993] $)

    $( Introduce conjunct to both sides of an implication. $)
    anim2i $p |- ( ( ch /\ ph ) -> ( ch /\ ps ) ) $=
      ( id anim12i ) CCABCEDF $.
      $( [5-Aug-1993] $)
  $}

  ${
    anim12ii.1 $e |- ( ph -> ( ps -> ch ) ) $.
    anim12ii.2 $e |- ( th -> ( ps -> ta ) ) $.
    $( Conjoin antecedents and consequents in a deduction.  (The proof was
       shortened by Wolf Lammen, 19-Jul-2013.) $)
    anim12ii $p |- ( ( ph /\ th ) -> ( ps -> ( ch /\ ta ) ) ) $=
      ( wa wi adantr adantl jcad ) ADHBCEABCIDFJDBEIAGKL $.
      $( [19-Jul-2013] $) $( [11-Nov-2007] $)
  $}

  $( Theorem *3.47 of [WhiteheadRussell] p. 113.  It was proved by Leibniz, and
     it evidently pleased him enough to call it 'praeclarum theorema' (splendid
     theorem).  (The proof was shortened by Wolf Lammen, 7-Apr-2013.) $)
  prth $p |- ( ( ( ph -> ps ) /\ ( ch -> th ) ) ->
              ( ( ph /\ ch ) -> ( ps /\ th ) ) ) $=
    ( wi wa simpl simpr anim12d ) ABEZCDEZFABCDJKGJKHI $.
    $( [7-Apr-2013] $) $( [12-Aug-1993] $)

  $( Theorem *2.3 of [WhiteheadRussell] p. 104. $)
  pm2.3 $p |- ( ( ph \/ ( ps \/ ch ) ) -> ( ph \/ ( ch \/ ps ) ) ) $=
    ( wo pm1.4 orim2i ) BCDCBDABCEF $.
    $( [3-Jan-2005] $)

  $( Theorem *2.41 of [WhiteheadRussell] p. 106. $)
  pm2.41 $p |- ( ( ps \/ ( ph \/ ps ) ) -> ( ph \/ ps ) ) $=
    ( wo olc id jaoi ) BABCZGBADGEF $.
    $( [3-Jan-2005] $)

  $( Theorem *2.42 of [WhiteheadRussell] p. 106. $)
  pm2.42 $p |- ( ( -. ph \/ ( ph -> ps ) ) -> ( ph -> ps ) ) $=
    ( wn wi pm2.21 id jaoi ) ACABDZHABEHFG $.
    $( [3-Jan-2005] $)

  $( Theorem *2.4 of [WhiteheadRussell] p. 106. $)
  pm2.4 $p |- ( ( ph \/ ( ph \/ ps ) ) -> ( ph \/ ps ) ) $=
    ( wo orc id jaoi ) AABCZGABDGEF $.
    $( [3-Jan-2005] $)

  ${
    pm2.65da.1 $e |- ( ( ph /\ ps ) -> ch ) $.
    pm2.65da.2 $e |- ( ( ph /\ ps ) -> -. ch ) $.
    $( Deduction rule for proof by contradiction. $)
    pm2.65da $p |- ( ph -> -. ps ) $=
      ( ex wn pm2.65d ) ABCABCDFABCGEFH $.
      $( [12-Jun-2014] $)
  $}

  $( Theorem *4.44 of [WhiteheadRussell] p. 119. $)
  pm4.44 $p |- ( ph <-> ( ph \/ ( ph /\ ps ) ) ) $=
    ( wa wo orc id simpl jaoi impbii ) AAABCZDAJEAAJAFABGHI $.
    $( [3-Jan-2005] $)

  $( Theorem *4.14 of [WhiteheadRussell] p. 117.  (The proof was shortened by
     Wolf Lammen, 23-Oct-2012.) $)
  pm4.14 $p |- ( ( ( ph /\ ps ) -> ch ) <-> ( ( ph /\ -. ch ) -> -. ps ) ) $=
    ( wi wn wa con34b imbi2i impexp 3bitr4i ) ABCDZDACEZBEZDZDABFCDALFMDKNABCGH
    ABCIALMIJ $.
    $( [23-Oct-2012] $) $( [3-Jan-2005] $)

  $( Theorem *3.37 (Transp) of [WhiteheadRussell] p. 112.  (The proof was
     shortened by Wolf Lammen, 23-Oct-2012.) $)
  pm3.37 $p |- ( ( ( ph /\ ps ) -> ch ) -> ( ( ph /\ -. ch ) -> -. ps ) ) $=
    ( wa wi wn pm4.14 biimpi ) ABDCEACFDBFEABCGH $.
    $( [23-Oct-2012] $) $( [3-Jan-2005] $)

  $( Theorem to move a conjunct in and out of a negation. $)
  nan $p |- ( ( ph -> -. ( ps /\ ch ) ) <-> ( ( ph /\ ps ) -> -. ch ) ) $=
    ( wa wn wi impexp imnan imbi2i bitr2i ) ABDCEZFABKFZFABCDEZFABKGLMABCHIJ $.
    $( [9-Nov-2003] $)

  $( Theorem *4.15 of [WhiteheadRussell] p. 117.  (The proof was shortened by
     Wolf Lammen, 18-Nov-2012.) $)
  pm4.15 $p |- ( ( ( ph /\ ps ) -> -. ch ) <-> ( ( ps /\ ch ) -> -. ph ) ) $=
    ( wa wn wi con2b nan bitr2i ) BCDZAEFAJEFABDCEFJAGABCHI $.
    $( [18-Nov-2012] $) $( [3-Jan-2005] $)

  $( Theorem *4.78 of [WhiteheadRussell] p. 121.  (The proof was shortened by
     Wolf Lammen, 19-Nov-2012.) $)
  pm4.78 $p |- ( ( ( ph -> ps ) \/ ( ph -> ch ) ) <->
                ( ph -> ( ps \/ ch ) ) ) $=
    ( wn wo wi orordi imor orbi12i 3bitr4ri ) ADZBCEZEKBEZKCEZEALFABFZACFZEKBCG
    ALHOMPNABHACHIJ $.
    $( [19-Nov-2012] $) $( [3-Jan-2005] $)

  $( Theorem *4.79 of [WhiteheadRussell] p. 121.  (The proof was shortened by
     Wolf Lammen, 27-Jun-2013.) $)
  pm4.79 $p |- ( ( ( ps -> ph ) \/ ( ch -> ph ) ) <->
                ( ( ps /\ ch ) -> ph ) ) $=
    ( wi wo wa id jaoa wn simplim pm3.3 syl5 orrd impbii ) BADZCADZEBCFADZOBAPC
    OGPGHQOPOIBQPBAJBCAKLMN $.
    $( [27-Jun-2013] $) $( [3-Jan-2005] $)

  $( Theorem *4.87 of [WhiteheadRussell] p. 122.  (The proof was shortened by
     Eric Schmidt, 26-Oct-2006.) $)
  pm4.87 $p |- ( ( ( ( ( ph /\ ps ) -> ch ) <-> ( ph -> ( ps -> ch ) ) ) /\
                ( ( ph -> ( ps -> ch ) ) <-> ( ps -> ( ph -> ch ) ) ) ) /\
                ( ( ps -> ( ph -> ch ) ) <-> ( ( ps /\ ph ) -> ch ) ) ) $=
    ( wa wi wb impexp bi2.04 pm3.2i bicomi ) ABDCEABCEEZFZKBACEEZFZDMBADCEZFLNA
    BCGABCHIOMBACGJI $.
    $( [27-Oct-2006] $) $( [3-Jan-2005] $)

  $( Theorem *3.33 (Syll) of [WhiteheadRussell] p. 112. $)
  pm3.33 $p |- ( ( ( ph -> ps ) /\ ( ps -> ch ) ) -> ( ph -> ch ) ) $=
    ( wi imim1 imp ) ABDBCDACDABCEF $.
    $( [3-Jan-2005] $)

  $( Theorem *3.34 (Syll) of [WhiteheadRussell] p. 112. $)
  pm3.34 $p |- ( ( ( ps -> ch ) /\ ( ph -> ps ) ) -> ( ph -> ch ) ) $=
    ( wi imim2 imp ) BCDABDACDBCAEF $.
    $( [3-Jan-2005] $)

  $( Conjunctive detachment.  Theorem *3.35 of [WhiteheadRussell] p. 112. $)
  pm3.35 $p |- ( ( ph /\ ( ph -> ps ) ) -> ps ) $=
    ( wi pm2.27 imp ) AABCBABDE $.
    $( [14-Dec-2002] $)

  $( Theorem *5.31 of [WhiteheadRussell] p. 125. $)
  pm5.31 $p |- ( ( ch /\ ( ph -> ps ) ) -> ( ph -> ( ps /\ ch ) ) ) $=
    ( wi wa pm3.21 imim2d imp ) CABDABCEZDCBIACBFGH $.
    $( [3-Jan-2005] $)

  ${
    imp4.1 $e |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ) $.
    $( An importation inference. $)
    imp4a $p |- ( ph -> ( ps -> ( ( ch /\ th ) -> ta ) ) ) $=
      ( wi wa impexp syl6ibr ) ABCDEGGCDHEGFCDEIJ $.
      $( [26-Apr-1994] $)

    $( An importation inference. $)
    imp4b $p |- ( ( ph /\ ps ) -> ( ( ch /\ th ) -> ta ) ) $=
      ( wa wi imp4a imp ) ABCDGEHABCDEFIJ $.
      $( [26-Apr-1994] $)

    $( An importation inference. $)
    imp4c $p |- ( ph -> ( ( ( ps /\ ch ) /\ th ) -> ta ) ) $=
      ( wa wi imp3a ) ABCGDEABCDEHFII $.
      $( [26-Apr-1994] $)

    $( An importation inference. $)
    imp4d $p |- ( ph -> ( ( ps /\ ( ch /\ th ) ) -> ta ) ) $=
      ( wa imp4a imp3a ) ABCDGEABCDEFHI $.
      $( [26-Apr-1994] $)

    $( An importation inference. $)
    imp41 $p |- ( ( ( ( ph /\ ps ) /\ ch ) /\ th ) -> ta ) $=
      ( wa wi imp imp31 ) ABGCDEABCDEHHFIJ $.
      $( [26-Apr-1994] $)

    $( An importation inference. $)
    imp42 $p |- ( ( ( ph /\ ( ps /\ ch ) ) /\ th ) -> ta ) $=
      ( wa wi imp32 imp ) ABCGGDEABCDEHFIJ $.
      $( [26-Apr-1994] $)

    $( An importation inference. $)
    imp43 $p |- ( ( ( ph /\ ps ) /\ ( ch /\ th ) ) -> ta ) $=
      ( wa imp4b imp ) ABGCDGEABCDEFHI $.
      $( [26-Apr-1994] $)

    $( An importation inference. $)
    imp44 $p |- ( ( ph /\ ( ( ps /\ ch ) /\ th ) ) -> ta ) $=
      ( wa imp4c imp ) ABCGDGEABCDEFHI $.
      $( [26-Apr-1994] $)

    $( An importation inference. $)
    imp45 $p |- ( ( ph /\ ( ps /\ ( ch /\ th ) ) ) -> ta ) $=
      ( wa imp4d imp ) ABCDGGEABCDEFHI $.
      $( [26-Apr-1994] $)

  $}

  ${
    imp5.1 $e |- ( ph -> ( ps -> ( ch -> ( th -> ( ta -> et ) ) ) ) ) $.
    $( An importation inference.  (Contributed by Jeff Hankins, 7-Jul-2009.) $)
    imp5a $p |- ( ph -> ( ps -> ( ch -> ( ( th /\ ta ) -> et ) ) ) ) $=
      ( wi wa pm3.31 syl8 ) ABCDEFHHDEIFHGDEFJK $.
      $( [7-Jul-2009] $)

    $( An importation inference.  (Contributed by Jeff Hankins, 7-Jul-2009.) $)
    imp5d $p |- ( ( ( ph /\ ps ) /\ ch ) -> ( ( th /\ ta ) -> et ) ) $=
      ( wa wi imp31 imp3a ) ABHCHDEFABCDEFIIGJK $.
      $( [7-Jul-2009] $)

    $( An importation inference.  (Contributed by Jeff Hankins, 7-Jul-2009.) $)
    imp5g $p |- ( ( ph /\ ps ) -> ( ( ( ch /\ th ) /\ ta ) -> et ) ) $=
      ( wa wi imp imp4c ) ABHCDEFABCDEFIIIGJK $.
      $( [7-Jul-2009] $)

    $( An importation inference.  (Contributed by Jeff Hankins, 7-Jul-2009.) $)
    imp55 $p |- ( ( ( ph /\ ( ps /\ ( ch /\ th ) ) ) /\ ta ) -> et ) $=
      ( wa wi imp4a imp42 ) ABCDHEFABCDEFIGJK $.
      $( [7-Jul-2009] $)

    $( An importation inference.  (Contributed by Jeff Hankins, 7-Jul-2009.) $)
    imp511 $p |- ( ( ph /\ ( ( ps /\ ( ch /\ th ) ) /\ ta ) ) -> et ) $=
      ( wa wi imp4a imp44 ) ABCDHEFABCDEFIGJK $.
      $( [7-Jul-2009] $)
  $}

  ${
    expimpd.1 $e |- ( ( ph /\ ps ) -> ( ch -> th ) ) $.
    $( Exportation followed by a deduction version of importation. $)
    expimpd $p |- ( ph -> ( ( ps /\ ch ) -> th ) ) $=
      ( wi ex imp3a ) ABCDABCDFEGH $.
      $( [6-Sep-2008] $)
  $}

  ${
    exp31.1 $e |- ( ( ( ph /\ ps ) /\ ch ) -> th ) $.
    $( An exportation inference. $)
    exp31 $p |- ( ph -> ( ps -> ( ch -> th ) ) ) $=
      ( wi wa ex ) ABCDFABGCDEHH $.
      $( [26-Apr-1994] $)
  $}

  ${
    exp32.1 $e |- ( ( ph /\ ( ps /\ ch ) ) -> th ) $.
    $( An exportation inference. $)
    exp32 $p |- ( ph -> ( ps -> ( ch -> th ) ) ) $=
      ( wa ex exp3a ) ABCDABCFDEGH $.
      $( [26-Apr-1994] $)
  $}

  ${
    exp4a.1 $e |- ( ph -> ( ps -> ( ( ch /\ th ) -> ta ) ) ) $.
    $( An exportation inference. $)
    exp4a $p |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ) $=
      ( wa wi impexp syl6ib ) ABCDGEHCDEHHFCDEIJ $.
      $( [26-Apr-1994] $)
  $}

  ${
    exp4b.1 $e |- ( ( ph /\ ps ) -> ( ( ch /\ th ) -> ta ) ) $.
    $( An exportation inference.  (The proof was shortened by Wolf Lammen,
       23-Nov-2012.) $)
    exp4b $p |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ) $=
      ( wa wi ex exp4a ) ABCDEABCDGEHFIJ $.
      $( [23-Nov-2012] $) $( [26-Apr-1994] $)
  $}

  ${
    exp4c.1 $e |- ( ph -> ( ( ( ps /\ ch ) /\ th ) -> ta ) ) $.
    $( An exportation inference. $)
    exp4c $p |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ) $=
      ( wi wa exp3a ) ABCDEGABCHDEFII $.
      $( [26-Apr-1994] $)
  $}

  ${
    exp4d.1 $e |- ( ph -> ( ( ps /\ ( ch /\ th ) ) -> ta ) ) $.
    $( An exportation inference. $)
    exp4d $p |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ) $=
      ( wa exp3a exp4a ) ABCDEABCDGEFHI $.
      $( [26-Apr-1994] $)
  $}

  ${
    exp41.1 $e |- ( ( ( ( ph /\ ps ) /\ ch ) /\ th ) -> ta ) $.
    $( An exportation inference. $)
    exp41 $p |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ) $=
      ( wi wa ex exp31 ) ABCDEGABHCHDEFIJ $.
      $( [26-Apr-1994] $)
  $}

  ${
    exp42.1 $e |- ( ( ( ph /\ ( ps /\ ch ) ) /\ th ) -> ta ) $.
    $( An exportation inference. $)
    exp42 $p |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ) $=
      ( wi wa exp31 exp3a ) ABCDEGABCHDEFIJ $.
      $( [26-Apr-1994] $)
  $}

  ${
    exp43.1 $e |- ( ( ( ph /\ ps ) /\ ( ch /\ th ) ) -> ta ) $.
    $( An exportation inference. $)
    exp43 $p |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ) $=
      ( wa ex exp4b ) ABCDEABGCDGEFHI $.
      $( [26-Apr-1994] $)
  $}

  ${
    exp44.1 $e |- ( ( ph /\ ( ( ps /\ ch ) /\ th ) ) -> ta ) $.
    $( An exportation inference. $)
    exp44 $p |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ) $=
      ( wi wa exp32 exp3a ) ABCDEGABCHDEFIJ $.
      $( [26-Apr-1994] $)
  $}

  ${
    exp45.1 $e |- ( ( ph /\ ( ps /\ ( ch /\ th ) ) ) -> ta ) $.
    $( An exportation inference. $)
    exp45 $p |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ) $=
      ( wa exp32 exp4a ) ABCDEABCDGEFHI $.
      $( [26-Apr-1994] $)
  $}

  ${
    expr.1 $e |- ( ( ph /\ ( ps /\ ch ) ) -> th ) $.
    $( Export a wff from a right conjunct.  (Contributed by Jeff Hankins,
       30-Aug-2009.) $)
    expr $p |- ( ( ph /\ ps ) -> ( ch -> th ) ) $=
      ( wi exp32 imp ) ABCDFABCDEGH $.
      $( [21-Feb-2011] $) $( [28-Aug-2009] $)
  $}

  ${
    exp5c.1 $e |- ( ph -> ( ( ps /\ ch ) -> ( ( th /\ ta ) -> et ) ) ) $.
    $( An exportation inference.  (Contributed by Jeff Hankins, 7-Jul-2009.) $)
    exp5c $p |- ( ph -> ( ps -> ( ch -> ( th -> ( ta -> et ) ) ) ) ) $=
      ( wi wa exp4a exp3a ) ABCDEFHHABCIDEFGJK $.
      $( [7-Jul-2009] $)
  $}

  ${
    exp53.1 $e |- ( ( ( ( ph /\ ps ) /\ ( ch /\ th ) ) /\ ta ) -> et ) $.
    $( An exportation inference.  (Contributed by Jeff Hankins,
       30-Aug-2009.) $)
    exp53 $p |- ( ph -> ( ps -> ( ch -> ( th -> ( ta -> et ) ) ) ) ) $=
      ( wi wa ex exp43 ) ABCDEFHABICDIIEFGJK $.
      $( [21-Feb-2011] $) $( [7-Jul-2009] $)
  $}

  ${
    expl.1 $e |- ( ( ( ph /\ ps ) /\ ch ) -> th ) $.
    $( Export a wff from a left conjunct.  (Contributed by Jeff Hankins,
       28-Aug-2009.) $)
    expl $p |- ( ph -> ( ( ps /\ ch ) -> th ) ) $=
      ( exp31 imp3a ) ABCDABCDEFG $.
      $( [28-Aug-2009] $)
  $}

  ${
    impr.1 $e |- ( ( ph /\ ps ) -> ( ch -> th ) ) $.
    $( Import a wff into a right conjunct.  (Contributed by Jeff Hankins,
       30-Aug-2009.) $)
    impr $p |- ( ( ph /\ ( ps /\ ch ) ) -> th ) $=
      ( wi ex imp32 ) ABCDABCDFEGH $.
      $( [21-Feb-2011] $) $( [28-Aug-2009] $)
  $}

  ${
    impl.1 $e |- ( ph -> ( ( ps /\ ch ) -> th ) ) $.
    $( Export a wff from a left conjunct.  (Contributed by Mario Carneiro,
       9-Jul-2014.) $)
    impl $p |- ( ( ( ph /\ ps ) /\ ch ) -> th ) $=
      ( exp3a imp31 ) ABCDABCDEFG $.
      $( [9-Jul-2014] $)
  $}

  ${
    impac.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Importation with conjunction in consequent. $)
    impac $p |- ( ( ph /\ ps ) -> ( ch /\ ps ) ) $=
      ( wa ancrd imp ) ABCBEABCDFG $.
      $( [9-Aug-1994] $)
  $}

  ${
    exbiri.1 $e |- ( ( ph /\ ps ) -> ( ch <-> th ) ) $.
    $( Inference form of ~ exbir .  This proof is ~ exbiriVD automatically
       translated and minimized.  (Contributed by Alan Sare, 31-Dec-2011.)
       (The proof was shortened by Wolf Lammen, 27-Jan-2013.) $)
    exbiri $p |- ( ph -> ( ps -> ( th -> ch ) ) ) $=
      ( wa biimpar exp31 ) ABDCABFCDEGH $.
      $( [27-Jan-2013] $) $( [31-Dec-2011] $)
  $}

  ${
    pm3.26bda.1 $e |- ( ph -> ( ps <-> ( ch /\ th ) ) ) $.
    $( Deduction eliminating a conjunct. $)
    simprbda $p |- ( ( ph /\ ps ) -> ch ) $=
      ( wa biimpa simpld ) ABFCDABCDFEGH $.
      $( [22-Oct-2007] $)

    $( Deduction eliminating a conjunct. $)
    simplbda $p |- ( ( ph /\ ps ) -> th ) $=
      ( wa biimpa simprd ) ABFCDABCDFEGH $.
      $( [22-Oct-2007] $)
  $}

  ${
    pm3.26bi2.1 $e |- ( ph <-> ( ps /\ ch ) ) $.
    $( Deduction eliminating a conjunct.  Automatically derived from
       ~ simplbi2VD .  (Contributed by Alan Sare, 31-Dec-2011.) $)
    simplbi2 $p |- ( ps -> ( ch -> ph ) ) $=
      ( wa biimpri ex ) BCAABCEDFG $.
      $( [31-Dec-2011] $)
  $}

  $( A theorem similar to the standard definition of the biconditional.
     Definition of [Margaris] p. 49. $)
  dfbi2 $p |- ( ( ph <-> ps ) <-> ( ( ph -> ps ) /\ ( ps -> ph ) ) ) $=
    ( wb wi wn wa dfbi1 df-an bitr4i ) ABCABDZBADZEDEJKFABGJKHI $.
    $( [5-Aug-1993] $)

  $( Definition ~ df-bi rewritten in an abbreviated form to help intuitive
     understanding of that definition.  Note that it is a conjunction of two
     implications; one which asserts properties that follow from the
     biconditional and one which asserts properties that imply the
     biconditional. $)
  dfbi $p |- ( ( ( ph <-> ps ) -> ( ( ph -> ps ) /\ ( ps -> ph ) ) )
        /\ ( ( ( ph -> ps ) /\ ( ps -> ph ) ) -> ( ph <-> ps ) ) ) $=
    ( wb wi wa dfbi2 biimpi biimpri pm3.2i ) ABCZABDBADEZDKJDJKABFZGJKLHI $.
    $( [15-Aug-2008] $)

  $( Implication in terms of biconditional and conjunction.  Theorem *4.71 of
     [WhiteheadRussell] p. 120.  (The proof was shortened by Wolf Lammen,
     2-Dec-2012.) $)
  pm4.71 $p |- ( ( ph -> ps ) <-> ( ph <-> ( ph /\ ps ) ) ) $=
    ( wa wi wb simpl biantru anclb dfbi2 3bitr4i ) AABCZDZLKADZCABDAKEMLABFGABH
    AKIJ $.
    $( [2-Dec-2012] $) $( [5-Aug-1993] $)

  $( Implication in terms of biconditional and conjunction.  Theorem *4.71 of
     [WhiteheadRussell] p. 120 (with conjunct reversed). $)
  pm4.71r $p |- ( ( ph -> ps ) <-> ( ph <-> ( ps /\ ph ) ) ) $=
    ( wi wa wb pm4.71 ancom bibi2i bitri ) ABCAABDZEABADZEABFJKAABGHI $.
    $( [25-Jul-1999] $)

  ${
    pm4.71i.1 $e |- ( ph -> ps ) $.
    $( Inference converting an implication to a biconditional with
       conjunction.  Inference from Theorem *4.71 of [WhiteheadRussell]
       p. 120. $)
    pm4.71i $p |- ( ph <-> ( ph /\ ps ) ) $=
      ( wi wa wb pm4.71 mpbi ) ABDAABEFCABGH $.
      $( [4-Jan-2004] $)
  $}

  ${
    pm4.71ri.1 $e |- ( ph -> ps ) $.
    $( Inference converting an implication to a biconditional with
       conjunction.  Inference from Theorem *4.71 of [WhiteheadRussell] p. 120
       (with conjunct reversed). $)
    pm4.71ri $p |- ( ph <-> ( ps /\ ph ) ) $=
      ( wi wa wb pm4.71r mpbi ) ABDABAEFCABGH $.
      $( [1-Dec-2003] $)
  $}

  ${
    pm4.71rd.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Deduction converting an implication to a biconditional with
       conjunction.  Deduction from Theorem *4.71 of [WhiteheadRussell]
       p. 120. $)
    pm4.71rd $p |- ( ph -> ( ps <-> ( ch /\ ps ) ) ) $=
      ( wi wa wb pm4.71r sylib ) ABCEBCBFGDBCHI $.
      $( [10-Feb-2005] $)
  $}

  $( Distribution of implication over biconditional.  Theorem *5.32 of
     [WhiteheadRussell] p. 125. $)
  pm5.32 $p |- ( ( ph -> ( ps <-> ch ) ) <->
               ( ( ph /\ ps ) <-> ( ph /\ ch ) ) ) $=
    ( wb wi wn wa notbi imbi2i pm5.74 3bitri df-an bibi12i bitr4i ) ABCDZEZABFZ
    EZFZACFZEZFZDZABGZACGZDPAQTDZERUADUCOUFABCHIAQTJRUAHKUDSUEUBABLACLMN $.
    $( [1-Aug-1994] $)

  ${
    pm5.32i.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Distribution of implication over biconditional (inference rule). $)
    pm5.32i $p |- ( ( ph /\ ps ) <-> ( ph /\ ch ) ) $=
      ( wb wi wa pm5.32 mpbi ) ABCEFABGACGEDABCHI $.
      $( [1-Aug-1994] $)

    $( Distribution of implication over biconditional (inference rule). $)
    pm5.32ri $p |- ( ( ps /\ ph ) <-> ( ch /\ ph ) ) $=
      ( wa pm5.32i ancom 3bitr4i ) ABEACEBAECAEABCDFBAGCAGH $.
      $( [12-Mar-1995] $)
  $}

  ${
    pm5.32d.1 $e |- ( ph -> ( ps -> ( ch <-> th ) ) ) $.
    $( Distribution of implication over biconditional (deduction rule). $)
    pm5.32d $p |- ( ph -> ( ( ps /\ ch ) <-> ( ps /\ th ) ) ) $=
      ( wb wi wa pm5.32 sylib ) ABCDFGBCHBDHFEBCDIJ $.
      $( [29-Oct-1996] $)

    $( Distribution of implication over biconditional (deduction rule). $)
    pm5.32rd $p |- ( ph -> ( ( ch /\ ps ) <-> ( th /\ ps ) ) ) $=
      ( wa pm5.32d ancom 3bitr4g ) ABCFBDFCBFDBFABCDEGCBHDBHI $.
      $( [25-Dec-2004] $)
  $}

  ${
    pm5.32da.1 $e |- ( ( ph /\ ps ) -> ( ch <-> th ) ) $.
    $( Distribution of implication over biconditional (deduction rule). $)
    pm5.32da $p |- ( ph -> ( ( ps /\ ch ) <-> ( ps /\ th ) ) ) $=
      ( wb ex pm5.32d ) ABCDABCDFEGH $.
      $( [9-Dec-2006] $)
  $}

  ${
    biadan2.1 $e |- ( ph -> ps ) $.
    biadan2.2 $e |- ( ps -> ( ph <-> ch ) ) $.
    $( Add a conjunction to an equivalence.  (Contributed by Jeff Madsen,
       20-Jun-2011.) $)
    biadan2 $p |- ( ph <-> ( ps /\ ch ) ) $=
      ( wa pm4.71ri pm5.32i bitri ) ABAFBCFABDGBACEHI $.
      $( [20-Jun-2011] $)
  $}

  $( Theorem *4.24 of [WhiteheadRussell] p. 117. $)
  pm4.24 $p |- ( ph <-> ( ph /\ ph ) ) $=
    ( id pm4.71i ) AAABC $.
    $( [14-Mar-2014] $) $( [3-Jan-2005] $)

  $( Idempotent law for conjunction.  (The proof was shortened by Wolf Lammen,
     14-Mar-2014.) $)
  anidm $p |- ( ( ph /\ ph ) <-> ph ) $=
    ( wa pm4.24 bicomi ) AAABACD $.
    $( [14-Mar-2014] $) $( [5-Aug-1993] $)

  $( Obsolete proof of ~ anidm as of 14-Mar-2014. $)
  anidmOLD $p |- ( ( ph /\ ph ) <-> ph ) $=
    ( wa simpl id ancli impbii ) AABAAACAAADEF $.
    $( [6-Nov-2012] $) $( [5-Aug-1993] $)

  $( Obsolete proof of ~ pm4.24 as of 14-Mar-2014. $)
  pm4.24OLD $p |- ( ph <-> ( ph /\ ph ) ) $=
    ( wa anidm bicomi ) AABAACD $.
    $( [3-Jan-2005] $)

  ${
    anidms.1 $e |- ( ( ph /\ ph ) -> ps ) $.
    $( Inference from idempotent law for conjunction. $)
    anidms $p |- ( ph -> ps ) $=
      ( ex pm2.43i ) ABAABCDE $.
      $( [15-Jun-1994] $)
  $}

  $( Conjunction idempotence with antecedent.  (Contributed by Roy F. Longton,
     8-Aug-2005.) $)
  anidmdbi $p |- ( ( ph -> ( ps /\ ps ) ) <-> ( ph -> ps ) ) $=
    ( wa anidm imbi2i ) BBCBABDE $.
    $( [8-Aug-2005] $)

  ${
    anasss.1 $e |- ( ( ( ph /\ ps ) /\ ch ) -> th ) $.
    $( Associative law for conjunction applied to antecedent (eliminates
       syllogism). $)
    anasss $p |- ( ( ph /\ ( ps /\ ch ) ) -> th ) $=
      ( exp31 imp32 ) ABCDABCDEFG $.
      $( [15-Nov-2002] $)
  $}

  ${
    anassrs.1 $e |- ( ( ph /\ ( ps /\ ch ) ) -> th ) $.
    $( Associative law for conjunction applied to antecedent (eliminates
       syllogism). $)
    anassrs $p |- ( ( ( ph /\ ps ) /\ ch ) -> th ) $=
      ( exp32 imp31 ) ABCDABCDEFG $.
      $( [15-Nov-2002] $)
  $}

  $( Associative law for conjunction.  Theorem *4.32 of [WhiteheadRussell]
     p. 118.  (The proof was shortened by Wolf Lammen, 24-Nov-2012.) $)
  anass $p |- ( ( ( ph /\ ps ) /\ ch ) <-> ( ph /\ ( ps /\ ch ) ) ) $=
    ( wa id anassrs anasss impbii ) ABDCDZABCDDZABCJJEFABCIIEGH $.
    $( [24-Nov-2012] $) $( [5-Aug-1993] $)

  ${
    sylanl1.1 $e |- ( ph -> ps ) $.
    sylanl1.2 $e |- ( ( ( ps /\ ch ) /\ th ) -> ta ) $.
    $( A syllogism inference. $)
    sylanl1 $p |- ( ( ( ph /\ ch ) /\ th ) -> ta ) $=
      ( wa anim1i sylan ) ACHBCHDEABCFIGJ $.
      $( [10-Mar-2005] $)
  $}

  ${
    sylanl2.1 $e |- ( ph -> ch ) $.
    sylanl2.2 $e |- ( ( ( ps /\ ch ) /\ th ) -> ta ) $.
    $( A syllogism inference. $)
    sylanl2 $p |- ( ( ( ps /\ ph ) /\ th ) -> ta ) $=
      ( wa anim2i sylan ) BAHBCHDEACBFIGJ $.
      $( [1-Jan-2005] $)
  $}

  ${
    sylanr1.1 $e |- ( ph -> ch ) $.
    sylanr1.2 $e |- ( ( ps /\ ( ch /\ th ) ) -> ta ) $.
    $( A syllogism inference. $)
    sylanr1 $p |- ( ( ps /\ ( ph /\ th ) ) -> ta ) $=
      ( wa anim1i sylan2 ) ADHBCDHEACDFIGJ $.
      $( [9-Apr-2005] $)
  $}

  ${
    sylanr2.1 $e |- ( ph -> th ) $.
    sylanr2.2 $e |- ( ( ps /\ ( ch /\ th ) ) -> ta ) $.
    $( A syllogism inference. $)
    sylanr2 $p |- ( ( ps /\ ( ch /\ ph ) ) -> ta ) $=
      ( wa anim2i sylan2 ) CAHBCDHEADCFIGJ $.
      $( [9-Apr-2005] $)
  $}

  ${
    sylani.1 $e |- ( ph -> ch ) $.
    sylani.2 $e |- ( ps -> ( ( ch /\ th ) -> ta ) ) $.
    $( A syllogism inference. $)
    sylani $p |- ( ps -> ( ( ph /\ th ) -> ta ) ) $=
      ( wi a1i syland ) BACDEACHBFIGJ $.
      $( [2-May-1996] $)
  $}

  ${
    sylan2i.1 $e |- ( ph -> th ) $.
    sylan2i.2 $e |- ( ps -> ( ( ch /\ th ) -> ta ) ) $.
    $( A syllogism inference. $)
    sylan2i $p |- ( ps -> ( ( ch /\ ph ) -> ta ) ) $=
      ( wi a1i sylan2d ) BADCEADHBFIGJ $.
      $( [1-Aug-1994] $)
  $}

  ${
    syl2ani.1 $e |- ( ph -> ch ) $.
    syl2ani.2 $e |- ( et -> th ) $.
    syl2ani.3 $e |- ( ps -> ( ( ch /\ th ) -> ta ) ) $.
    $( A syllogism inference. $)
    syl2ani $p |- ( ps -> ( ( ph /\ et ) -> ta ) ) $=
      ( sylan2i sylani ) ABCFEGFBCDEHIJK $.
      $( [3-Aug-1999] $)
  $}

  ${
    sylan9.1 $e |- ( ph -> ( ps -> ch ) ) $.
    sylan9.2 $e |- ( th -> ( ch -> ta ) ) $.
    $( Nested syllogism inference conjoining dissimilar antecedents.  (The
       proof was shortened by Andrew Salmon, 7-May-2011.) $)
    sylan9 $p |- ( ( ph /\ th ) -> ( ps -> ta ) ) $=
      ( wi syl9 imp ) ADBEHABCDEFGIJ $.
      $( [12-May-2011] $) $( [5-Aug-1993] $)
  $}

  ${
    sylan9r.1 $e |- ( ph -> ( ps -> ch ) ) $.
    sylan9r.2 $e |- ( th -> ( ch -> ta ) ) $.
    $( Nested syllogism inference conjoining dissimilar antecedents. $)
    sylan9r $p |- ( ( th /\ ph ) -> ( ps -> ta ) ) $=
      ( wi syl9r imp ) DABEHABCDEFGIJ $.
      $( [5-Aug-1993] $)
  $}

  ${
    mtand.1 $e |- ( ph -> -. ch ) $.
    mtand.2 $e |- ( ( ph /\ ps ) -> ch ) $.
    $( A modus tollens deduction.  (Contributed by Jeff Hankins,
       19-Aug-2009.) $)
    mtand $p |- ( ph -> -. ps ) $=
      ( ex mtod ) ABCDABCEFG $.
      $( [21-Feb-2011] $) $( [15-Jul-2009] $)
  $}

  ${
    mtord.1 $e |- ( ph -> -. ch ) $.
    mtord.2 $e |- ( ph -> -. th ) $.
    mtord.3 $e |- ( ph -> ( ps -> ( ch \/ th ) ) ) $.
    $( A modus tollens deduction involving disjunction.  (Contributed by Jeff
       Hankins, 15-Jul-2009.) $)
    mtord $p |- ( ph -> -. ps ) $=
      ( wn wo wi df-or syl6ib mpid mtod ) ABDFABCHZDEABCDIODJGCDKLMN $.
      $( [15-Jul-2009] $)
  $}

  ${
    syl2anc.1 $e |- ( ph -> ps ) $.
    syl2anc.2 $e |- ( ph -> ch ) $.
    syl2anc.3 $e |- ( ( ps /\ ch ) -> th ) $.
    $( Syllogism inference combined with contraction. $)
    syl2anc $p |- ( ph -> th ) $=
      ( ex sylc ) ABCDEFBCDGHI $.
      $( [16-Mar-2012] $)
  $}

  ${
    sylancl.1 $e |- ( ph -> ps ) $.
    sylancl.2 $e |- ch $.
    sylancl.3 $e |- ( ( ps /\ ch ) -> th ) $.
    $( Syllogism inference combined with modus ponens.  (Contributed by Jeff
       Madsen, 2-Sep-2009.) $)
    sylancl $p |- ( ph -> th ) $=
      ( a1i syl2anc ) ABCDECAFHGI $.
      $( [18-Apr-2010] $) $( [2-Sep-2009] $)
  $}

  ${
    sylancr.1 $e |- ps $.
    sylancr.2 $e |- ( ph -> ch ) $.
    sylancr.3 $e |- ( ( ps /\ ch ) -> th ) $.
    $( Syllogism inference combined with modus ponens.  (Contributed by Jeff
       Madsen, 2-Sep-2009.) $)
    sylancr $p |- ( ph -> th ) $=
      ( a1i syl2anc ) ABCDBAEHFGI $.
      $( [2-Sep-2009] $)
  $}

  ${
    sylanbrc.1 $e |- ( ph -> ps ) $.
    sylanbrc.2 $e |- ( ph -> ch ) $.
    sylanbrc.3 $e |- ( th <-> ( ps /\ ch ) ) $.
    $( Syllogism inference.  (Contributed by Jeff Madsen, 2-Sep-2009.) $)
    sylanbrc $p |- ( ph -> th ) $=
      ( wa jca sylibr ) ABCHDABCEFIGJ $.
      $( [11-Oct-2010] $) $( [2-Sep-2009] $)
  $}

  ${
    sylancb.1 $e |- ( ph <-> ps ) $.
    sylancb.2 $e |- ( ph <-> ch ) $.
    sylancb.3 $e |- ( ( ps /\ ch ) -> th ) $.
    $( A syllogism inference combined with contraction. $)
    sylancb $p |- ( ph -> th ) $=
      ( syl2anb anidms ) ADABCDAEFGHI $.
      $( [3-Sep-2004] $)
  $}

  ${
    sylancbr.1 $e |- ( ps <-> ph ) $.
    sylancbr.2 $e |- ( ch <-> ph ) $.
    sylancbr.3 $e |- ( ( ps /\ ch ) -> th ) $.
    $( A syllogism inference combined with contraction. $)
    sylancbr $p |- ( ph -> th ) $=
      ( syl2anbr anidms ) ADABCDAEFGHI $.
      $( [3-Sep-2004] $)
  $}

  ${
    sylancom.1 $e |- ( ( ph /\ ps ) -> ch ) $.
    sylancom.2 $e |- ( ( ch /\ ps ) -> th ) $.
    $( Syllogism inference with commutation of antecents. $)
    sylancom $p |- ( ( ph /\ ps ) -> th ) $=
      ( wa simpr syl2anc ) ABGCBDEABHFI $.
      $( [2-Jul-2008] $)
  $}

  ${
    mpdan.1 $e |- ( ph -> ps ) $.
    mpdan.2 $e |- ( ( ph /\ ps ) -> ch ) $.
    $( An inference based on modus ponens.  (The proof was shortened by Wolf
       Lammen, 22-Nov-2012.) $)
    mpdan $p |- ( ph -> ch ) $=
      ( id syl2anc ) AABCAFDEG $.
      $( [22-Nov-2012] $) $( [23-May-1999] $)
  $}

  ${
    mpancom.1 $e |- ( ps -> ph ) $.
    mpancom.2 $e |- ( ( ph /\ ps ) -> ch ) $.
    $( An inference based on modus ponens with commutation of antecedents.
       (The proof was shortened by Wolf Lammen, 7-Apr-2013.) $)
    mpancom $p |- ( ps -> ch ) $=
      ( id syl2anc ) BABCDBFEG $.
      $( [7-Apr-2013] $) $( [28-Oct-2003] $)
  $}

  ${
    mpan.1 $e |- ph $.
    mpan.2 $e |- ( ( ph /\ ps ) -> ch ) $.
    $( An inference based on modus ponens.  (The proof was shortened by Wolf
       Lammen, 7-Apr-2013.) $)
    mpan $p |- ( ps -> ch ) $=
      ( a1i mpancom ) ABCABDFEG $.
      $( [7-Apr-2013] $) $( [30-Aug-1993] $)
  $}

  ${
    mpan2.1 $e |- ps $.
    mpan2.2 $e |- ( ( ph /\ ps ) -> ch ) $.
    $( An inference based on modus ponens.  (The proof was shortened by Wolf
       Lammen, 19-Nov-2012.) $)
    mpan2 $p |- ( ph -> ch ) $=
      ( a1i mpdan ) ABCBADFEG $.
      $( [19-Nov-2012] $) $( [16-Sep-1993] $)
  $}

  ${
    mp2an.1 $e |- ph $.
    mp2an.2 $e |- ps $.
    mp2an.3 $e |- ( ( ph /\ ps ) -> ch ) $.
    $( An inference based on modus ponens. $)
    mp2an $p |- ch $=
      ( mpan ax-mp ) BCEABCDFGH $.
      $( [13-Apr-1995] $)
  $}

  ${
    mp4an.1 $e |- ph $.
    mp4an.2 $e |- ps $.
    mp4an.3 $e |- ch $.
    mp4an.4 $e |- th $.
    mp4an.5 $e |- ( ( ( ph /\ ps ) /\ ( ch /\ th ) ) -> ta ) $.
    $( An inference based on modus ponens.  (Contributed by Jeff Madsen,
       15-Jun-2011.) $)
    mp4an $p |- ta $=
      ( wa pm3.2i mp2an ) ABKCDKEABFGLCDHILJM $.
      $( [15-Jun-2010] $)
  $}

  ${
    mpan2d.1 $e |- ( ph -> ch ) $.
    mpan2d.2 $e |- ( ph -> ( ( ps /\ ch ) -> th ) ) $.
    $( A deduction based on modus ponens. $)
    mpan2d $p |- ( ph -> ( ps -> th ) ) $=
      ( exp3a mpid ) ABCDEABCDFGH $.
      $( [12-Dec-2004] $)
  $}

  ${
    mpand.1 $e |- ( ph -> ps ) $.
    mpand.2 $e |- ( ph -> ( ( ps /\ ch ) -> th ) ) $.
    $( A deduction based on modus ponens.  (The proof was shortened by Wolf
       Lammen, 7-Apr-2013.) $)
    mpand $p |- ( ph -> ( ch -> th ) ) $=
      ( ancomsd mpan2d ) ACBDEABCDFGH $.
      $( [7-Apr-2013] $) $( [12-Dec-2004] $)
  $}

  ${
    mpani.1 $e |- ps $.
    mpani.2 $e |- ( ph -> ( ( ps /\ ch ) -> th ) ) $.
    $( An inference based on modus ponens.  (The proof was shortened by Wolf
       Lammen, 19-Nov-2012.) $)
    mpani $p |- ( ph -> ( ch -> th ) ) $=
      ( a1i mpand ) ABCDBAEGFH $.
      $( [19-Nov-2012] $) $( [10-Apr-1994] $)
  $}

  ${
    mpan2i.1 $e |- ch $.
    mpan2i.2 $e |- ( ph -> ( ( ps /\ ch ) -> th ) ) $.
    $( An inference based on modus ponens.  (The proof was shortened by Wolf
       Lammen, 19-Nov-2012.) $)
    mpan2i $p |- ( ph -> ( ps -> th ) ) $=
      ( a1i mpan2d ) ABCDCAEGFH $.
      $( [19-Nov-2012] $) $( [10-Apr-1994] $)
  $}

  ${
    mp2ani.1 $e |- ps $.
    mp2ani.2 $e |- ch $.
    mp2ani.3 $e |- ( ph -> ( ( ps /\ ch ) -> th ) ) $.
    $( An inference based on modus ponens. $)
    mp2ani $p |- ( ph -> th ) $=
      ( mpani mpi ) ACDFABCDEGHI $.
      $( [12-Dec-2004] $)
  $}

  ${
    mp2and.1 $e |- ( ph -> ps ) $.
    mp2and.2 $e |- ( ph -> ch ) $.
    mp2and.3 $e |- ( ph -> ( ( ps /\ ch ) -> th ) ) $.
    $( A deduction based on modus ponens. $)
    mp2and $p |- ( ph -> th ) $=
      ( mpand mpd ) ACDFABCDEGHI $.
      $( [12-Dec-2004] $)
  $}

  ${
    mpanl1.1 $e |- ph $.
    mpanl1.2 $e |- ( ( ( ph /\ ps ) /\ ch ) -> th ) $.
    $( An inference based on modus ponens.  (The proof was shortened by Wolf
       Lammen, 7-Apr-2013.) $)
    mpanl1 $p |- ( ( ps /\ ch ) -> th ) $=
      ( wa jctl sylan ) BABGCDBAEHFI $.
      $( [7-Apr-2013] $) $( [16-Aug-1994] $)
  $}

  ${
    mpanl2.1 $e |- ps $.
    mpanl2.2 $e |- ( ( ( ph /\ ps ) /\ ch ) -> th ) $.
    $( An inference based on modus ponens.  (The proof was shortened by Andrew
       Salmon, 7-May-2011.) $)
    mpanl2 $p |- ( ( ph /\ ch ) -> th ) $=
      ( wa jctr sylan ) AABGCDABEHFI $.
      $( [22-Nov-2012] $) $( [16-Aug-1994] $)
  $}

  ${
    mpanl12.1 $e |- ph $.
    mpanl12.2 $e |- ps $.
    mpanl12.3 $e |- ( ( ( ph /\ ps ) /\ ch ) -> th ) $.
    $( An inference based on modus ponens. $)
    mpanl12 $p |- ( ch -> th ) $=
      ( mpanl1 mpan ) BCDFABCDEGHI $.
      $( [13-Jul-2005] $)
  $}

  ${
    mpanr1.1 $e |- ps $.
    mpanr1.2 $e |- ( ( ph /\ ( ps /\ ch ) ) -> th ) $.
    $( An inference based on modus ponens.  (The proof was shortened by Andrew
       Salmon, 7-May-2011.) $)
    mpanr1 $p |- ( ( ph /\ ch ) -> th ) $=
      ( anassrs mpanl2 ) ABCDEABCDFGH $.
      $( [12-May-2011] $) $( [3-May-1994] $)
  $}

  ${
    mpanr2.1 $e |- ch $.
    mpanr2.2 $e |- ( ( ph /\ ( ps /\ ch ) ) -> th ) $.
    $( An inference based on modus ponens.  (The proof was shortened by Andrew
       Salmon, 7-May-2011.)  (The proof was shortened by Wolf Lammen,
       7-Apr-2013.) $)
    mpanr2 $p |- ( ( ph /\ ps ) -> th ) $=
      ( wa jctr sylan2 ) BABCGDBCEHFI $.
      $( [7-Apr-2013] $) $( [3-May-1994] $)
  $}

  ${
    mpanr12.1 $e |- ps $.
    mpanr12.2 $e |- ch $.
    mpanr12.3 $e |- ( ( ph /\ ( ps /\ ch ) ) -> th ) $.
    $( An inference based on modus ponens. $)
    mpanr12 $p |- ( ph -> th ) $=
      ( mpanr1 mpan2 ) ACDFABCDEGHI $.
      $( [24-Jul-2009] $)
  $}

  ${
    mpanlr1.1 $e |- ps $.
    mpanlr1.2 $e |- ( ( ( ph /\ ( ps /\ ch ) ) /\ th ) -> ta ) $.
    $( An inference based on modus ponens.  (The proof was shortened by Wolf
       Lammen, 7-Apr-2013.) $)
    mpanlr1 $p |- ( ( ( ph /\ ch ) /\ th ) -> ta ) $=
      ( wa jctl sylanl2 ) CABCHDECBFIGJ $.
      $( [7-Apr-2013] $) $( [30-Dec-2004] $)
  $}

  ${
    pm5.74da.1 $e |- ( ( ph /\ ps ) -> ( ch <-> th ) ) $.
    $( Distribution of implication over biconditional (deduction rule). $)
    pm5.74da $p |- ( ph -> ( ( ps -> ch ) <-> ( ps -> th ) ) ) $=
      ( wb ex pm5.74d ) ABCDABCDFEGH $.
      $( [4-May-2007] $)
  $}

  $( Theorem *4.45 of [WhiteheadRussell] p. 119. $)
  pm4.45 $p |- ( ph <-> ( ph /\ ( ph \/ ps ) ) ) $=
    ( wo orc pm4.71i ) AABCABDE $.
    $( [3-Jan-2005] $)

  $( Distribution of implication with conjunction.  (The proof was shortened by
     Wolf Lammen, 6-Dec-2012.) $)
  imdistan $p |- ( ( ph -> ( ps -> ch ) ) <->
                ( ( ph /\ ps ) -> ( ph /\ ch ) ) ) $=
    ( wi wa pm5.42 impexp bitr4i ) ABCDDABACEZDDABEIDABCFABIGH $.
    $( [6-Dec-2012] $) $( [31-May-1999] $)

  ${
    imdistani.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Distribution of implication with conjunction. $)
    imdistani $p |- ( ( ph /\ ps ) -> ( ph /\ ch ) ) $=
      ( wa anc2li imp ) ABACEABCDFG $.
      $( [1-Aug-1994] $)
  $}

  ${
    imdistanri.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Distribution of implication with conjunction. $)
    imdistanri $p |- ( ( ps /\ ph ) -> ( ch /\ ph ) ) $=
      ( com12 impac ) BACABCDEF $.
      $( [8-Jan-2002] $)
  $}

  ${
    imdistand.1 $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
    $( Distribution of implication with conjunction (deduction rule). $)
    imdistand $p |- ( ph -> ( ( ps /\ ch ) -> ( ps /\ th ) ) ) $=
      ( wi wa imdistan sylib ) ABCDFFBCGBDGFEBCDHI $.
      $( [27-Aug-2004] $)
  $}

  ${
    imdistanda.1 $e |- ( ( ph /\ ps ) -> ( ch -> th ) ) $.
    $( Distribution of implication with conjunction (deduction version with
       conjoined antecedent).  (Contributed by Jeff Madsen, 19-Jun-2011.) $)
    imdistanda $p |- ( ph -> ( ( ps /\ ch ) -> ( ps /\ th ) ) ) $=
      ( wi ex imdistand ) ABCDABCDFEGH $.
      $( [19-Jun-2011] $)
  $}

  ${
    bi.aa $e |- ( ph <-> ps ) $.
    $( Introduce a left conjunct to both sides of a logical equivalence.  (The
       proof was shortened by Wolf Lammen, 16-Nov-2013.) $)
    anbi2i $p |- ( ( ch /\ ph ) <-> ( ch /\ ps ) ) $=
      ( wb a1i pm5.32i ) CABABECDFG $.
      $( [16-Nov-2013] $) $( [5-Aug-1993] $)

    $( Introduce a right conjunct to both sides of a logical equivalence.  (The
       proof was shortened by Wolf Lammen, 16-Nov-2013.) $)
    anbi1i $p |- ( ( ph /\ ch ) <-> ( ps /\ ch ) ) $=
      ( wb a1i pm5.32ri ) CABABECDFG $.
      $( [16-Nov-2013] $) $( [5-Aug-1993] $)
  $}

  ${
    anbi12.1 $e |- ( ph <-> ps ) $.
    anbi12.2 $e |- ( ch <-> th ) $.
    $( Conjoin both sides of two equivalences. $)
    anbi12i $p |- ( ( ph /\ ch ) <-> ( ps /\ th ) ) $=
      ( wa anbi1i anbi2i bitri ) ACGBCGBDGABCEHCDBFIJ $.
      $( [5-Aug-1993] $)
  $}

  ${
    sylan9bb.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    sylan9bb.2 $e |- ( th -> ( ch <-> ta ) ) $.
    $( Nested syllogism inference conjoining dissimilar antecedents. $)
    sylan9bb $p |- ( ( ph /\ th ) -> ( ps <-> ta ) ) $=
      ( wa wb adantr adantl bitrd ) ADHBCEABCIDFJDCEIAGKL $.
      $( [4-Mar-1995] $)
  $}

  ${
    sylan9bbr.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    sylan9bbr.2 $e |- ( th -> ( ch <-> ta ) ) $.
    $( Nested syllogism inference conjoining dissimilar antecedents. $)
    sylan9bbr $p |- ( ( th /\ ph ) -> ( ps <-> ta ) ) $=
      ( wb sylan9bb ancoms ) ADBEHABCDEFGIJ $.
      $( [4-Mar-1995] $)
  $}

  ${
    bid.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Deduction adding a left disjunct to both sides of a logical
       equivalence. $)
    orbi2d $p |- ( ph -> ( ( th \/ ps ) <-> ( th \/ ch ) ) ) $=
      ( wn wi wo imbi2d df-or 3bitr4g ) ADFZBGLCGDBHDCHABCLEIDBJDCJK $.
      $( [5-Aug-1993] $)

    $( Deduction adding a right disjunct to both sides of a logical
       equivalence. $)
    orbi1d $p |- ( ph -> ( ( ps \/ th ) <-> ( ch \/ th ) ) ) $=
      ( wo orbi2d orcom 3bitr4g ) ADBFDCFBDFCDFABCDEGBDHCDHI $.
      $( [5-Aug-1993] $)

    $( Deduction adding a left conjunct to both sides of a logical
       equivalence.  (The proof was shortened by Wolf Lammen, 16-Nov-2013.) $)
    anbi2d $p |- ( ph -> ( ( th /\ ps ) <-> ( th /\ ch ) ) ) $=
      ( wb a1d pm5.32d ) ADBCABCFDEGH $.
      $( [16-Nov-2013] $) $( [5-Aug-1993] $)

    $( Deduction adding a right conjunct to both sides of a logical
       equivalence.  (The proof was shortened by Wolf Lammen, 16-Nov-2013.) $)
    anbi1d $p |- ( ph -> ( ( ps /\ th ) <-> ( ch /\ th ) ) ) $=
      ( wb a1d pm5.32rd ) ADBCABCFDEGH $.
      $( [16-Nov-2013] $) $( [5-Aug-1993] $)
  $}

  $( Theorem *4.37 of [WhiteheadRussell] p. 118. $)
  orbi1 $p |- ( ( ph <-> ps ) -> ( ( ph \/ ch ) <-> ( ps \/ ch ) ) ) $=
    ( wb id orbi1d ) ABDZABCGEF $.
    $( [3-Jan-2005] $)

  $( Introduce a right conjunct to both sides of a logical equivalence.
     Theorem *4.36 of [WhiteheadRussell] p. 118. $)
  anbi1 $p |- ( ( ph <-> ps ) -> ( ( ph /\ ch ) <-> ( ps /\ ch ) ) ) $=
    ( wb id anbi1d ) ABDZABCGEF $.
    $( [3-Jan-2005] $)

  $( Introduce a left conjunct to both sides of a logical equivalence. $)
  anbi2 $p |- ( ( ph <-> ps ) -> ( ( ch /\ ph ) <-> ( ch /\ ps ) ) ) $=
    ( wb id anbi2d ) ABDZABCGEF $.
    $( [16-Nov-2013] $)

  $( Theorem *4.22 of [WhiteheadRussell] p. 117. $)
  bitr $p |- ( ( ( ph <-> ps ) /\ ( ps <-> ch ) ) -> ( ph <-> ch ) ) $=
    ( wb bibi1 biimpar ) ABDACDBCDABCEF $.
    $( [3-Jan-2005] $)

  ${
    bi12d.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    bi12d.2 $e |- ( ph -> ( th <-> ta ) ) $.
    $( Deduction joining two equivalences to form equivalence of
       disjunctions. $)
    orbi12d $p |- ( ph -> ( ( ps \/ th ) <-> ( ch \/ ta ) ) ) $=
      ( wo orbi1d orbi2d bitrd ) ABDHCDHCEHABCDFIADECGJK $.
      $( [5-Aug-1993] $)

    $( Deduction joining two equivalences to form equivalence of
       conjunctions. $)
    anbi12d $p |- ( ph -> ( ( ps /\ th ) <-> ( ch /\ ta ) ) ) $=
      ( wa anbi1d anbi2d bitrd ) ABDHCDHCEHABCDFIADECGJK $.
      $( [5-Aug-1993] $)

  $}

  $( Theorem *5.3 of [WhiteheadRussell] p. 125.  (The proof was shortened by
     Andrew Salmon, 7-May-2011.) $)
  pm5.3 $p |- ( ( ( ph /\ ps ) -> ch ) <->
               ( ( ph /\ ps ) -> ( ph /\ ch ) ) ) $=
    ( wa wi impexp imdistan bitri ) ABDZCEABCEEIACDEABCFABCGH $.
    $( [12-May-2011] $) $( [3-Jan-2005] $)

  $( Theorem *5.61 of [WhiteheadRussell] p. 125.  (The proof was shortened by
     Wolf Lammen, 30-Jun-2013.) $)
  pm5.61 $p |- ( ( ( ph \/ ps ) /\ -. ps ) <-> ( ph /\ -. ps ) ) $=
    ( wn wo biorf orcom syl6rbb pm5.32ri ) BCZABDZAIABADJBAEBAFGH $.
    $( [30-Jun-2013] $) $( [3-Jan-2005] $)

  ${
    adant2.1 $e |- ( ( ph /\ ps ) -> ch ) $.
    $( Deduction adding a conjunct to antecedent.  (The proof was shortened by
       Wolf Lammen, 24-Nov-2012.) $)
    adantll $p |- ( ( ( th /\ ph ) /\ ps ) -> ch ) $=
      ( wa simpr sylan ) DAFABCDAGEH $.
      $( [24-Nov-2012] $) $( [4-May-1994] $)

    $( Deduction adding a conjunct to antecedent.  (The proof was shortened by
       Wolf Lammen, 24-Nov-2012.) $)
    adantlr $p |- ( ( ( ph /\ th ) /\ ps ) -> ch ) $=
      ( wa simpl sylan ) ADFABCADGEH $.
      $( [24-Nov-2012] $) $( [4-May-1994] $)

    $( Deduction adding a conjunct to antecedent.  (The proof was shortened by
       Wolf Lammen, 24-Nov-2012.) $)
    adantrl $p |- ( ( ph /\ ( th /\ ps ) ) -> ch ) $=
      ( wa simpr sylan2 ) DBFABCDBGEH $.
      $( [24-Nov-2012] $) $( [4-May-1994] $)

    $( Deduction adding a conjunct to antecedent.  (The proof was shortened by
       Wolf Lammen, 24-Nov-2012.) $)
    adantrr $p |- ( ( ph /\ ( ps /\ th ) ) -> ch ) $=
      ( wa simpl sylan2 ) BDFABCBDGEH $.
      $( [24-Nov-2012] $) $( [4-May-1994] $)
  $}

  ${
    adantl2.1 $e |- ( ( ( ph /\ ps ) /\ ch ) -> th ) $.
    $( Deduction adding a conjunct to antecedent.  (The proof was shortened by
       Wolf Lammen, 2-Dec-2012.) $)
    adantlll $p |- ( ( ( ( ta /\ ph ) /\ ps ) /\ ch ) -> th ) $=
      ( wa simpr sylanl1 ) EAGABCDEAHFI $.
      $( [2-Dec-2012] $) $( [26-Dec-2004] $)

    $( Deduction adding a conjunct to antecedent.  (The proof was shortened by
       Wolf Lammen, 4-Dec-2012.) $)
    adantllr $p |- ( ( ( ( ph /\ ta ) /\ ps ) /\ ch ) -> th ) $=
      ( wa simpl sylanl1 ) AEGABCDAEHFI $.
      $( [4-Dec-2012] $) $( [26-Dec-2004] $)

    $( Deduction adding a conjunct to antecedent.  (The proof was shortened by
       Wolf Lammen, 4-Dec-2012.) $)
    adantlrl $p |- ( ( ( ph /\ ( ta /\ ps ) ) /\ ch ) -> th ) $=
      ( wa simpr sylanl2 ) EBGABCDEBHFI $.
      $( [4-Dec-2012] $) $( [26-Dec-2004] $)

    $( Deduction adding a conjunct to antecedent.  (The proof was shortened by
       Wolf Lammen, 4-Dec-2012.) $)
    adantlrr $p |- ( ( ( ph /\ ( ps /\ ta ) ) /\ ch ) -> th ) $=
      ( wa simpl sylanl2 ) BEGABCDBEHFI $.
      $( [4-Dec-2012] $) $( [26-Dec-2004] $)
  $}

  ${
    adantr2.1 $e |- ( ( ph /\ ( ps /\ ch ) ) -> th ) $.
    $( Deduction adding a conjunct to antecedent.  (The proof was shortened by
       Wolf Lammen, 4-Dec-2012.) $)
    adantrll $p |- ( ( ph /\ ( ( ta /\ ps ) /\ ch ) ) -> th ) $=
      ( wa simpr sylanr1 ) EBGABCDEBHFI $.
      $( [4-Dec-2012] $) $( [26-Dec-2004] $)

    $( Deduction adding a conjunct to antecedent.  (The proof was shortened by
       Wolf Lammen, 4-Dec-2012.) $)
    adantrlr $p |- ( ( ph /\ ( ( ps /\ ta ) /\ ch ) ) -> th ) $=
      ( wa simpl sylanr1 ) BEGABCDBEHFI $.
      $( [4-Dec-2012] $) $( [26-Dec-2004] $)

    $( Deduction adding a conjunct to antecedent.  (The proof was shortened by
       Wolf Lammen, 4-Dec-2012.) $)
    adantrrl $p |- ( ( ph /\ ( ps /\ ( ta /\ ch ) ) ) -> th ) $=
      ( wa simpr sylanr2 ) ECGABCDECHFI $.
      $( [4-Dec-2012] $) $( [26-Dec-2004] $)

    $( Deduction adding a conjunct to antecedent.  (The proof was shortened by
       Wolf Lammen, 4-Dec-2012.) $)
    adantrrr $p |- ( ( ph /\ ( ps /\ ( ch /\ ta ) ) ) -> th ) $=
      ( wa simpl sylanr2 ) CEGABCDCEHFI $.
      $( [4-Dec-2012] $) $( [26-Dec-2004] $)
  $}

  ${
    ad2ant.1 $e |- ( ph -> ps ) $.
    $( Deduction adding conjuncts to antecedent.  (The proof was shortened by
       Wolf Lammen, 20-Nov-2012.) $)
    ad2antrr $p |- ( ( ( ph /\ ch ) /\ th ) -> ps ) $=
      ( adantr adantlr ) ADBCABDEFG $.
      $( [20-Nov-2012] $) $( [19-Oct-1999] $)

    $( Deduction adding 3 conjuncts to antecedent. $)
    ad3antrrr $p |- ( ( ( ( ph /\ ch ) /\ th ) /\ ta ) -> ps ) $=
      ( wa adantr ad2antrr ) ACGBDEABCFHI $.
      $( [28-Jul-2012] $)

    $( Deduction adding conjuncts to antecedent.  (The proof was shortened by
       Wolf Lammen, 20-Nov-2012.) $)
    ad2antlr $p |- ( ( ( ch /\ ph ) /\ th ) -> ps ) $=
      ( adantr adantll ) ADBCABDEFG $.
      $( [20-Nov-2012] $) $( [19-Oct-1999] $)

    $( Deduction adding conjuncts to antecedent. $)
    ad2antrl $p |- ( ( ch /\ ( ph /\ th ) ) -> ps ) $=
      ( wa adantr adantl ) ADFBCABDEGH $.
      $( [19-Oct-1999] $)

    $( Deduction adding conjuncts to antecedent. $)
    ad2antll $p |- ( ( ch /\ ( th /\ ph ) ) -> ps ) $=
      ( wa adantl ) DAFBCABDEGG $.
      $( [19-Oct-1999] $)
  $}

  ${
    ad2ant2.1 $e |- ( ( ph /\ ps ) -> ch ) $.
    $( Deduction adding two conjuncts to antecedent. $)
    ad2ant2l $p |- ( ( ( th /\ ph ) /\ ( ta /\ ps ) ) -> ch ) $=
      ( wa adantrl adantll ) AEBGCDABCEFHI $.
      $( [8-Jan-2006] $)

    $( Deduction adding two conjuncts to antecedent. $)
    ad2ant2r $p |- ( ( ( ph /\ th ) /\ ( ps /\ ta ) ) -> ch ) $=
      ( wa adantrr adantlr ) ABEGCDABCEFHI $.
      $( [8-Jan-2006] $)

    $( Deduction adding two conjuncts to antecedent. $)
    ad2ant2lr $p |- ( ( ( th /\ ph ) /\ ( ps /\ ta ) ) -> ch ) $=
      ( wa adantrr adantll ) ABEGCDABCEFHI $.
      $( [23-Nov-2007] $)

    $( Deduction adding two conjuncts to antecedent. $)
    ad2ant2rl $p |- ( ( ( ph /\ th ) /\ ( ta /\ ps ) ) -> ch ) $=
      ( wa adantrl adantlr ) AEBGCDABCEFHI $.
      $( [24-Nov-2007] $)
  $}

  $( Simplification of a conjunction. $)
  simpll $p |- ( ( ( ph /\ ps ) /\ ch ) -> ph ) $=
    ( id ad2antrr ) AABCADE $.
    $( [18-Mar-2007] $)

  $( Simplification of a conjunction. $)
  simplr $p |- ( ( ( ph /\ ps ) /\ ch ) -> ps ) $=
    ( id ad2antlr ) BBACBDE $.
    $( [20-Mar-2007] $)

  $( Simplification of a conjunction. $)
  simprl $p |- ( ( ph /\ ( ps /\ ch ) ) -> ps ) $=
    ( id ad2antrl ) BBACBDE $.
    $( [21-Mar-2007] $)

  $( Simplification of a conjunction. $)
  simprr $p |- ( ( ph /\ ( ps /\ ch ) ) -> ch ) $=
    ( id ad2antll ) CCABCDE $.
    $( [21-Mar-2007] $)

  $( Simplification of a conjunction.  (Contributed by Jeff Hankins,
     28-Jul-2009.) $)
  simplll $p |- ( ( ( ( ph /\ ps ) /\ ch ) /\ th ) -> ph ) $=
    ( wa simpl ad2antrr ) ABEACDABFG $.
    $( [18-Apr-2010] $) $( [28-Jul-2009] $)

  $( Simplification of a conjunction.  (Contributed by Jeff Hankins,
     28-Jul-2009.) $)
  simpllr $p |- ( ( ( ( ph /\ ps ) /\ ch ) /\ th ) -> ps ) $=
    ( wa simpr ad2antrr ) ABEBCDABFG $.
    $( [18-Apr-2010] $) $( [28-Jul-2009] $)

  $( Simplification of a conjunction.  (Contributed by Jeff Hankins,
     28-Jul-2009.) $)
  simplrl $p |- ( ( ( ph /\ ( ps /\ ch ) ) /\ th ) -> ps ) $=
    ( wa simpl ad2antlr ) BCEBADBCFG $.
    $( [18-Apr-2010] $) $( [28-Jul-2009] $)

  $( Simplification of a conjunction.  (Contributed by Jeff Hankins,
     28-Jul-2009.) $)
  simplrr $p |- ( ( ( ph /\ ( ps /\ ch ) ) /\ th ) -> ch ) $=
    ( wa simpr ad2antlr ) BCECADBCFG $.
    $( [18-Apr-2010] $) $( [28-Jul-2009] $)

  $( Simplification of a conjunction.  (Contributed by Jeff Hankins,
     28-Jul-2009.) $)
  simprll $p |- ( ( ph /\ ( ( ps /\ ch ) /\ th ) ) -> ps ) $=
    ( wa simpl ad2antrl ) BCEBADBCFG $.
    $( [18-Apr-2010] $) $( [28-Jul-2009] $)

  $( Simplification of a conjunction.  (Contributed by Jeff Hankins,
     28-Jul-2009.) $)
  simprlr $p |- ( ( ph /\ ( ( ps /\ ch ) /\ th ) ) -> ch ) $=
    ( wa simpr ad2antrl ) BCECADBCFG $.
    $( [18-Apr-2010] $) $( [28-Jul-2009] $)

  $( Simplification of a conjunction.  (Contributed by Jeff Hankins,
     28-Jul-2009.) $)
  simprrl $p |- ( ( ph /\ ( ps /\ ( ch /\ th ) ) ) -> ch ) $=
    ( wa simpl ad2antll ) CDECABCDFG $.
    $( [18-Apr-2010] $) $( [28-Jul-2009] $)

  $( Simplification of a conjunction.  (Contributed by Jeff Hankins,
     28-Jul-2009.) $)
  simprrr $p |- ( ( ph /\ ( ps /\ ( ch /\ th ) ) ) -> th ) $=
    ( wa simpr ad2antll ) CDEDABCDFG $.
    $( [18-Apr-2010] $) $( [28-Jul-2009] $)

  $( Disjunction of antecedents.  Compare Theorem *4.77 of [WhiteheadRussell]
     p. 121.  (The proof was shortened by Wolf Lammen, 9-Dec-2012.) $)
  jaob $p |- ( ( ( ph \/ ch ) -> ps ) <-> ( ( ph -> ps ) /\ ( ch -> ps ) ) ) $=
    ( wo wi wa pm2.67-2 olc imim1i jca pm3.44 impbii ) ACDZBEZABEZCBEZFNOPABCGC
    MBCAHIJBACKL $.
    $( [9-Dec-2012] $) $( [30-May-1994] $)

  ${
    jaoian.1 $e |- ( ( ph /\ ps ) -> ch ) $.
    jaoian.2 $e |- ( ( th /\ ps ) -> ch ) $.
    $( Inference disjoining the antecedents of two implications. $)
    jaoian $p |- ( ( ( ph \/ th ) /\ ps ) -> ch ) $=
      ( wo wi ex jaoi imp ) ADGBCABCHDABCEIDBCFIJK $.
      $( [23-Oct-2005] $)
  $}

  ${
    jaodan.1 $e |- ( ( ph /\ ps ) -> ch ) $.
    jaodan.2 $e |- ( ( ph /\ th ) -> ch ) $.
    $( Deduction disjoining the antecedents of two implications. $)
    jaodan $p |- ( ( ph /\ ( ps \/ th ) ) -> ch ) $=
      ( wo ex jaod imp ) ABDGCABCDABCEHADCFHIJ $.
      $( [14-Oct-2005] $)
  $}

  $( Theorem *4.77 of [WhiteheadRussell] p. 121. $)
  pm4.77 $p |- ( ( ( ps -> ph ) /\ ( ch -> ph ) ) <->
                ( ( ps \/ ch ) -> ph ) ) $=
    ( wo wi wa jaob bicomi ) BCDAEBAECAEFBACGH $.
    $( [3-Jan-2005] $)

  $( Theorem *2.63 of [WhiteheadRussell] p. 107. $)
  pm2.63 $p |- ( ( ph \/ ps ) -> ( ( -. ph \/ ps ) -> ps ) ) $=
    ( wo wn pm2.53 idd jaod ) ABCZADBBABEHBFG $.
    $( [3-Jan-2005] $)

  $( Theorem *2.64 of [WhiteheadRussell] p. 107. $)
  pm2.64 $p |- ( ( ph \/ ps ) -> ( ( ph \/ -. ps ) -> ph ) ) $=
    ( wn wo wi ax-1 orel2 jaoi com12 ) ABCZDABDZAAKAEJAKFBAGHI $.
    $( [3-Jan-2005] $)

  ${
    pm2.61ian.1 $e |- ( ( ph /\ ps ) -> ch ) $.
    pm2.61ian.2 $e |- ( ( -. ph /\ ps ) -> ch ) $.
    $( Elimination of an antecedent. $)
    pm2.61ian $p |- ( ps -> ch ) $=
      ( wi ex wn pm2.61i ) ABCFABCDGAHBCEGI $.
      $( [1-Jan-2005] $)
  $}

  ${
    pm2.61dan.1 $e |- ( ( ph /\ ps ) -> ch ) $.
    pm2.61dan.2 $e |- ( ( ph /\ -. ps ) -> ch ) $.
    $( Elimination of an antecedent. $)
    pm2.61dan $p |- ( ph -> ch ) $=
      ( ex wn pm2.61d ) ABCABCDFABGCEFH $.
      $( [1-Jan-2005] $)
  $}

  ${
    pm2.61ddan.1 $e |- ( ( ph /\ ps ) -> th ) $.
    pm2.61ddan.2 $e |- ( ( ph /\ ch ) -> th ) $.
    pm2.61ddan.3 $e |- ( ( ph /\ ( -. ps /\ -. ch ) ) -> th ) $.
    $( Elimination of two antecedents. $)
    pm2.61ddan $p |- ( ph -> th ) $=
      ( wn wa adantlr anassrs pm2.61dan ) ABDEABHZICDACDMFJAMCHDGKLL $.
      $( [9-Jul-2013] $)
  $}

  ${
    pm2.61dda.1 $e |- ( ( ph /\ -. ps ) -> th ) $.
    pm2.61dda.2 $e |- ( ( ph /\ -. ch ) -> th ) $.
    pm2.61dda.3 $e |- ( ( ph /\ ( ps /\ ch ) ) -> th ) $.
    $( Elimination of two antecedents. $)
    pm2.61dda $p |- ( ph -> th ) $=
      ( wa anassrs wn adantlr pm2.61dan ) ABDABHCDABCDGIACJDBFKLEL $.
      $( [9-Jul-2013] $)
  $}

  ${
    condan.1 $e |- ( ( ph /\ -. ps ) -> ch ) $.
    condan.2 $e |- ( ( ph /\ -. ps ) -> -. ch ) $.
    $( Proof by contradiction.  (The proof was shortened by Wolf Lammen,
       19-Jun-2014.) $)
    condan $p |- ( ph -> ps ) $=
      ( wn pm2.65da notnot2 syl ) ABFZFBAJCDEGBHI $.
      $( [19-Jun-2014] $) $( [9-Feb-2006] $)
  $}

  $( Introduce one conjunct as an antecedent to the other.  "abai" stands for
     "and, biconditional, and, implication".  (The proof was shortened by Wolf
     Lammen, 7-Dec-2012.) $)
  abai $p |- ( ( ph /\ ps ) <-> ( ph /\ ( ph -> ps ) ) ) $=
    ( wi biimt pm5.32i ) ABABCABDE $.
    $( [7-Dec-2012] $) $( [12-Aug-1993] $)

  $( Theorem *5.53 of [WhiteheadRussell] p. 125. $)
  pm5.53 $p |- ( ( ( ( ph \/ ps ) \/ ch ) -> th ) <->
                ( ( ( ph -> th ) /\ ( ps -> th ) ) /\ ( ch -> th ) ) ) $=
    ( wo wi wa jaob anbi1i bitri ) ABEZCEDFKDFZCDFZGADFBDFGZMGKDCHLNMADBHIJ $.
    $( [3-Jan-2005] $)

  $( Swap two conjuncts.  Note that the first digit (1) in the label refers to
     the outer conjunct position, and the next digit (2) to the inner conjunct
     position. $)
  an12 $p |- ( ( ph /\ ( ps /\ ch ) ) <-> ( ps /\ ( ph /\ ch ) ) ) $=
    ( wa ancom anbi1i anass 3bitr3i ) ABDZCDBADZCDABCDDBACDDIJCABEFABCGBACGH $.
    $( [12-Mar-1995] $)

  $( A rearrangement of conjuncts.  (The proof was shortened by Wolf Lammen,
     25-Dec-2012.) $)
  an32 $p |- ( ( ( ph /\ ps ) /\ ch ) <-> ( ( ph /\ ch ) /\ ps ) ) $=
    ( wa anass an12 ancom 3bitri ) ABDCDABCDDBACDZDIBDABCEABCFBIGH $.
    $( [25-Dec-2012] $) $( [12-Mar-1995] $)

  $( A rearrangement of conjuncts.  (The proof was shortened by Wolf Lammen,
     31-Dec-2012.) $)
  an13 $p |- ( ( ph /\ ( ps /\ ch ) ) <-> ( ch /\ ( ps /\ ph ) ) ) $=
    ( wa an12 anass ancom 3bitr2i ) ABCDDBACDDBADZCDCIDABCEBACFICGH $.
    $( [31-Dec-2012] $) $( [24-Jun-2012] $)

  $( A rearrangement of conjuncts.  (The proof was shortened by Wolf Lammen,
     31-Dec-2012.) $)
  an31 $p |- ( ( ( ph /\ ps ) /\ ch ) <-> ( ( ch /\ ps ) /\ ph ) ) $=
    ( wa an13 anass 3bitr4i ) ABCDDCBADDABDCDCBDADABCEABCFCBAFG $.
    $( [31-Dec-2012] $) $( [24-Jun-2012] $)

  ${
    an12s.1 $e |- ( ( ph /\ ( ps /\ ch ) ) -> th ) $.
    $( Swap two conjuncts in antecedent.  The label suffix "s" means that
       ~ an12 is combined with ~ syl (or a variant). $)
    an12s $p |- ( ( ps /\ ( ph /\ ch ) ) -> th ) $=
      ( wa an12 sylbi ) BACFFABCFFDBACGEH $.
      $( [13-Mar-1996] $)

    $( Inference commuting a nested conjunction in antecedent.  (The proof was
       shortened by Wolf Lammen, 24-Nov-2012.) $)
    ancom2s $p |- ( ( ph /\ ( ch /\ ps ) ) -> th ) $=
      ( wa pm3.22 sylan2 ) CBFABCFDCBGEH $.
      $( [24-Nov-2012] $) $( [24-May-2006] $)

    $( Swap two conjuncts in antecedent. $)
    an13s $p |- ( ( ch /\ ( ps /\ ph ) ) -> th ) $=
      ( exp32 com13 imp32 ) CBADABCDABCDEFGH $.
      $( [31-May-2006] $)
  $}

  ${
    an32s.1 $e |- ( ( ( ph /\ ps ) /\ ch ) -> th ) $.
    $( Swap two conjuncts in antecedent. $)
    an32s $p |- ( ( ( ph /\ ch ) /\ ps ) -> th ) $=
      ( wa an32 sylbi ) ACFBFABFCFDACBGEH $.
      $( [13-Mar-1996] $)

    $( Inference commuting a nested conjunction in antecedent.  (The proof was
       shortened by Wolf Lammen, 24-Nov-2012.) $)
    ancom1s $p |- ( ( ( ps /\ ph ) /\ ch ) -> th ) $=
      ( wa pm3.22 sylan ) BAFABFCDBAGEH $.
      $( [24-Nov-2012] $) $( [24-May-2006] $)

    $( Swap two conjuncts in antecedent. $)
    an31s $p |- ( ( ( ch /\ ps ) /\ ph ) -> th ) $=
      ( exp31 com13 imp31 ) CBADABCDABCDEFGH $.
      $( [31-May-2006] $)
  $}

  $( Absorption into embedded conjunct.  (The proof was shortened by Wolf
     Lammen, 16-Nov-2013.) $)
  anabs1 $p |- ( ( ( ph /\ ps ) /\ ph ) <-> ( ph /\ ps ) ) $=
    ( wa simpl pm4.71i bicomi ) ABCZGACGAABDEF $.
    $( [16-Nov-2013] $) $( [4-Sep-1995] $)

  $( Absorption into embedded conjunct.  (The proof was shortened by Wolf
     Lammen, 9-Dec-2012.) $)
  anabs5 $p |- ( ( ph /\ ( ph /\ ps ) ) <-> ( ph /\ ps ) ) $=
    ( wa ibar bicomd pm5.32i ) AABCZBABGABDEF $.
    $( [9-Dec-2012] $) $( [20-Jul-1996] $)

  $( Absorption into embedded conjunct.  (The proof was shortened by Wolf
     Lammen, 17-Nov-2013.) $)
  anabs7 $p |- ( ( ps /\ ( ph /\ ps ) ) <-> ( ph /\ ps ) ) $=
    ( wa simpr pm4.71ri bicomi ) ABCZBGCGBABDEF $.
    $( [17-Nov-2013] $) $( [20-Jul-1996] $)

  ${
    anabsan.1 $e |- ( ( ( ph /\ ph ) /\ ps ) -> ch ) $.
    $( Absorption of antecedent with conjunction. $)
    anabsan $p |- ( ( ph /\ ps ) -> ch ) $=
      ( wa pm4.24 sylanb ) AAAEBCAFDG $.
      $( [18-Nov-2013] $) $( [24-Mar-1996] $)
  $}

  ${
    anabss1.1 $e |- ( ( ( ph /\ ps ) /\ ph ) -> ch ) $.
    $( Absorption of antecedent into conjunction.  (The proof was shortened by
       Wolf Lammen, 31-Dec-2012.) $)
    anabss1 $p |- ( ( ph /\ ps ) -> ch ) $=
      ( an32s anabsan ) ABCABACDEF $.
      $( [19-Nov-2013] $) $( [20-Jul-1996] $)
  $}

  ${
    anabss4.1 $e |- ( ( ( ps /\ ph ) /\ ps ) -> ch ) $.
    $( Absorption of antecedent into conjunction. $)
    anabss4 $p |- ( ( ph /\ ps ) -> ch ) $=
      ( anabss1 ancoms ) BACBACDEF $.
      $( [20-Jul-1996] $)
  $}

  ${
    anabss5.1 $e |- ( ( ph /\ ( ph /\ ps ) ) -> ch ) $.
    $( Absorption of antecedent into conjunction.  (The proof was shortened by
       Wolf Lammen, 1-Jan-2013.) $)
    anabss5 $p |- ( ( ph /\ ps ) -> ch ) $=
      ( anassrs anabsan ) ABCAABCDEF $.
      $( [1-Jan-2013] $) $( [10-May-1994] $)
  $}

  ${
    anabsi5.1 $e |- ( ph -> ( ( ph /\ ps ) -> ch ) ) $.
    $( Absorption of antecedent into conjunction.  (The proof was shortened by
       Wolf Lammen, 18-Nov-2013.) $)
    anabsi5 $p |- ( ( ph /\ ps ) -> ch ) $=
      ( wa imp anabss5 ) ABCAABECDFG $.
      $( [18-Nov-2013] $) $( [11-Jun-1995] $)
  $}

  ${
    anabsi6.1 $e |- ( ph -> ( ( ps /\ ph ) -> ch ) ) $.
    $( Absorption of antecedent into conjunction. $)
    anabsi6 $p |- ( ( ph /\ ps ) -> ch ) $=
      ( ancomsd anabsi5 ) ABCABACDEF $.
      $( [14-Aug-2000] $)
  $}

  ${
    anabsi7.1 $e |- ( ps -> ( ( ph /\ ps ) -> ch ) ) $.
    $( Absorption of antecedent into conjunction.  (The proof was shortened by
       Wolf Lammen, 18-Nov-2013.) $)
    anabsi7 $p |- ( ( ph /\ ps ) -> ch ) $=
      ( anabsi6 ancoms ) BACBACDEF $.
      $( [18-Nov-2013] $) $( [20-Jul-1996] $)
  $}

  ${
    anabsi8.1 $e |- ( ps -> ( ( ps /\ ph ) -> ch ) ) $.
    $( Absorption of antecedent into conjunction. $)
    anabsi8 $p |- ( ( ph /\ ps ) -> ch ) $=
      ( anabsi5 ancoms ) BACBACDEF $.
      $( [26-Sep-1999] $)
  $}

  ${
    anabss7.1 $e |- ( ( ps /\ ( ph /\ ps ) ) -> ch ) $.
    $( Absorption of antecedent into conjunction.  (The proof was shortened by
       Wolf Lammen, 19-Nov-2013.) $)
    anabss7 $p |- ( ( ph /\ ps ) -> ch ) $=
      ( anassrs anabss4 ) ABCBABCDEF $.
      $( [19-Nov-2013] $) $( [20-Jul-1996] $)
  $}

  ${
    anabsan2.1 $e |- ( ( ph /\ ( ps /\ ps ) ) -> ch ) $.
    $( Absorption of antecedent with conjunction. $)
    anabsan2 $p |- ( ( ph /\ ps ) -> ch ) $=
      ( an12s anabss7 ) ABCABBCDEF $.
      $( [1-Jan-2013] $) $( [10-May-2004] $)
  $}

  ${
    anabss3.1 $e |- ( ( ( ph /\ ps ) /\ ps ) -> ch ) $.
    $( Absorption of antecedent into conjunction.  (The proof was shortened by
       Wolf Lammen, 1-Jan-2013.) $)
    anabss3 $p |- ( ( ph /\ ps ) -> ch ) $=
      ( anasss anabsan2 ) ABCABBCDEF $.
      $( [1-Jan-2013] $) $( [20-Jul-1996] $)
  $}

  $( Rearrangement of 4 conjuncts. $)
  an4 $p |- ( ( ( ph /\ ps ) /\ ( ch /\ th ) ) <->
              ( ( ph /\ ch ) /\ ( ps /\ th ) ) ) $=
    ( wa an12 anbi2i anass 3bitr4i ) ABCDEZEZEACBDEZEZEABEJEACELEKMABCDFGABJHAC
    LHI $.
    $( [10-Jul-1994] $)

  $( Rearrangement of 4 conjuncts. $)
  an42 $p |- ( ( ( ph /\ ps ) /\ ( ch /\ th ) ) <->
                 ( ( ph /\ ch ) /\ ( th /\ ps ) ) ) $=
    ( wa an4 ancom anbi2i bitri ) ABECDEEACEZBDEZEJDBEZEABCDFKLJBDGHI $.
    $( [7-Feb-1996] $)

  ${
    an4s.1 $e |- ( ( ( ph /\ ps ) /\ ( ch /\ th ) ) -> ta ) $.
    $( Inference rearranging 4 conjuncts in antecedent. $)
    an4s $p |- ( ( ( ph /\ ch ) /\ ( ps /\ th ) ) -> ta ) $=
      ( wa an4 sylbi ) ACGBDGGABGCDGGEACBDHFI $.
      $( [10-Aug-1995] $)
  $}

  ${
    an41r3s.1 $e |- ( ( ( ph /\ ps ) /\ ( ch /\ th ) ) -> ta ) $.
    $( Inference rearranging 4 conjuncts in antecedent. $)
    an42s $p |- ( ( ( ph /\ ch ) /\ ( th /\ ps ) ) -> ta ) $=
      ( wa an4s ancom2s ) ACGBDEABCDEFHI $.
      $( [10-Aug-1995] $)
  $}

  $( Distribution of conjunction over conjunction. $)
  anandi $p |- ( ( ph /\ ( ps /\ ch ) ) <->
               ( ( ph /\ ps ) /\ ( ph /\ ch ) ) ) $=
    ( wa anidm anbi1i an4 bitr3i ) ABCDZDAADZIDABDACDDJAIAEFAABCGH $.
    $( [14-Aug-1995] $)

  $( Distribution of conjunction over conjunction. $)
  anandir $p |- ( ( ( ph /\ ps ) /\ ch ) <->
               ( ( ph /\ ch ) /\ ( ps /\ ch ) ) ) $=
    ( wa anidm anbi2i an4 bitr3i ) ABDZCDICCDZDACDBCDDJCICEFABCCGH $.
    $( [24-Aug-1995] $)

  ${
    anandis.1 $e |- ( ( ( ph /\ ps ) /\ ( ph /\ ch ) ) -> ta ) $.
    $( Inference that undistributes conjunction in the antecedent. $)
    anandis $p |- ( ( ph /\ ( ps /\ ch ) ) -> ta ) $=
      ( wa an4s anabsan ) ABCFDABACDEGH $.
      $( [7-Jun-2004] $)
  $}

  ${
    anandirs.1 $e |- ( ( ( ph /\ ch ) /\ ( ps /\ ch ) ) -> ta ) $.
    $( Inference that undistributes conjunction in the antecedent. $)
    anandirs $p |- ( ( ( ph /\ ps ) /\ ch ) -> ta ) $=
      ( wa an4s anabsan2 ) ABFCDACBCDEGH $.
      $( [7-Jun-2004] $)
  $}

  ${
    impbida.1 $e |- ( ( ph /\ ps ) -> ch ) $.
    impbida.2 $e |- ( ( ph /\ ch ) -> ps ) $.
    $( Deduce an equivalence from two implications. $)
    impbida $p |- ( ph -> ( ps <-> ch ) ) $=
      ( ex impbid ) ABCABCDFACBEFG $.
      $( [17-Feb-2007] $)
  $}

  $( Theorem *3.48 of [WhiteheadRussell] p. 114. $)
  pm3.48 $p |- ( ( ( ph -> ps ) /\ ( ch -> th ) ) ->
               ( ( ph \/ ch ) -> ( ps \/ th ) ) ) $=
    ( wi wo orc imim2i olc jaao ) ABEABDFZCDECBKABDGHDKCDBIHJ $.
    $( [1-Dec-2012] $) $( [28-Jan-1997] $)

  $( Theorem *3.45 (Fact) of [WhiteheadRussell] p. 113. $)
  pm3.45 $p |- ( ( ph -> ps ) -> ( ( ph /\ ch ) -> ( ps /\ ch ) ) ) $=
    ( wi id anim1d ) ABDZABCGEF $.
    $( [3-Jan-2005] $)

  ${
    im2an9.1 $e |- ( ph -> ( ps -> ch ) ) $.
    im2an9.2 $e |- ( th -> ( ta -> et ) ) $.
    $( Deduction joining nested implications to form implication of
       conjunctions. $)
    im2anan9 $p |- ( ( ph /\ th ) -> ( ( ps /\ ta ) -> ( ch /\ et ) ) ) $=
      ( wa wi adantr adantl anim12d ) ADIBCEFABCJDGKDEFJAHLM $.
      $( [29-Feb-1996] $)

    $( Deduction joining nested implications to form implication of
       conjunctions. $)
    im2anan9r $p |- ( ( th /\ ph ) -> ( ( ps /\ ta ) -> ( ch /\ et ) ) ) $=
      ( wa wi im2anan9 ancoms ) ADBEICFIJABCDEFGHKL $.
      $( [29-Feb-1996] $)
  $}

  ${
    anim12dan.1 $e |- ( ( ph /\ ps ) -> ch ) $.
    anim12dan.2 $e |- ( ( ph /\ th ) -> ta ) $.
    $( Conjoin antecedents and consequents in a deduction.  (Contributed by
       Mario Carneiro, 12-May-2014.) $)
    anim12dan $p |- ( ( ph /\ ( ps /\ th ) ) -> ( ch /\ ta ) ) $=
      ( wa ex anim12d imp ) ABDHCEHABCDEABCFIADEGIJK $.
      $( [12-May-2014] $)
  $}

  ${
    orim12d.1 $e |- ( ph -> ( ps -> ch ) ) $.
    orim12d.2 $e |- ( ph -> ( th -> ta ) ) $.
    $( Disjoin antecedents and consequents in a deduction. $)
    orim12d $p |- ( ph -> ( ( ps \/ th ) -> ( ch \/ ta ) ) ) $=
      ( wi wo pm3.48 syl2anc ) ABCHDEHBDICEIHFGBCDEJK $.
      $( [10-May-1994] $)
  $}

  ${
    orim1d.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Disjoin antecedents and consequents in a deduction. $)
    orim1d $p |- ( ph -> ( ( ps \/ th ) -> ( ch \/ th ) ) ) $=
      ( idd orim12d ) ABCDDEADFG $.
      $( [23-Apr-1995] $)

    $( Disjoin antecedents and consequents in a deduction. $)
    orim2d $p |- ( ph -> ( ( th \/ ps ) -> ( th \/ ch ) ) ) $=
      ( idd orim12d ) ADDBCADFEG $.
      $( [23-Apr-1995] $)
  $}

  $( Axiom *1.6 (Sum) of [WhiteheadRussell] p. 97. $)
  orim2 $p |- ( ( ps -> ch ) -> ( ( ph \/ ps ) -> ( ph \/ ch ) ) ) $=
    ( wi id orim2d ) BCDZBCAGEF $.
    $( [3-Jan-2005] $)

  $( Theorem *2.38 of [WhiteheadRussell] p. 105. $)
  pm2.38 $p |- ( ( ps -> ch ) -> ( ( ps \/ ph ) -> ( ch \/ ph ) ) ) $=
    ( wi id orim1d ) BCDZBCAGEF $.
    $( [6-Mar-2008] $)

  $( Theorem *2.36 of [WhiteheadRussell] p. 105. $)
  pm2.36 $p |- ( ( ps -> ch ) -> ( ( ph \/ ps ) -> ( ch \/ ph ) ) ) $=
    ( wo wi pm1.4 pm2.38 syl5 ) ABDBADBCECADABFABCGH $.
    $( [6-Mar-2008] $)

  $( Theorem *2.37 of [WhiteheadRussell] p. 105. $)
  pm2.37 $p |- ( ( ps -> ch ) -> ( ( ps \/ ph ) -> ( ph \/ ch ) ) ) $=
    ( wi wo pm2.38 pm1.4 syl6 ) BCDBAECAEACEABCFCAGH $.
    $( [6-Mar-2008] $)

  $( Theorem *2.73 of [WhiteheadRussell] p. 108. $)
  pm2.73 $p |- ( ( ph -> ps ) -> ( ( ( ph \/ ps ) \/ ch ) ->
                ( ps \/ ch ) ) ) $=
    ( wi wo pm2.621 orim1d ) ABDABEBCABFG $.
    $( [3-Jan-2005] $)

  $( Theorem *2.74 of [WhiteheadRussell] p. 108.  (The proof was shortened by
     Andrew Salmon, 7-May-2011.) $)
  pm2.74 $p |- ( ( ps -> ph ) -> ( ( ( ph \/ ps ) \/ ch ) ->
                ( ph \/ ch ) ) ) $=
    ( wi wo orel2 ax-1 ja orim1d ) BADABEZACBAJADBAFAJGHI $.
    $( [12-May-2011] $) $( [3-Jan-2005] $)

  $( Disjunction distributes over implication.  (Contributed by Wolf Lammen,
     5-Jan-2013.) $)
  orimdi $p |- ( ( ph \/ ( ps -> ch ) ) <->
                ( ( ph \/ ps ) -> ( ph \/ ch ) ) ) $=
    ( wn wi wo imdi df-or imbi12i 3bitr4i ) ADZBCEZEKBEZKCEZEALFABFZACFZEKBCGAL
    HOMPNABHACHIJ $.
    $( [5-Jan-2013] $)

  $( Theorem *2.76 of [WhiteheadRussell] p. 108. $)
  pm2.76 $p |- ( ( ph \/ ( ps -> ch ) ) ->
                ( ( ph \/ ps ) -> ( ph \/ ch ) ) ) $=
    ( wi wo orimdi biimpi ) ABCDEABEACEDABCFG $.
    $( [5-Jan-2013] $) $( [3-Jan-2005] $)

  $( Theorem *2.75 of [WhiteheadRussell] p. 108.  (The proof was shortened by
     Wolf Lammen, 4-Jan-2013.) $)
  pm2.75 $p |- ( ( ph \/ ps ) ->
                ( ( ph \/ ( ps -> ch ) ) -> ( ph \/ ch ) ) ) $=
    ( wi wo pm2.76 com12 ) ABCDEABEACEABCFG $.
    $( [4-Jan-2013] $) $( [3-Jan-2005] $)

  $( Theorem *2.8 of [WhiteheadRussell] p. 108.  (The proof was shortened by
     Wolf Lammen, 5-Jan-2013.) $)
  pm2.8 $p |- ( ( ph \/ ps ) -> ( ( -. ps \/ ch ) -> ( ph \/ ch ) ) ) $=
    ( wo wn pm2.53 con1d orim1d ) ABDZBEACIABABFGH $.
    $( [5-Jan-2013] $) $( [3-Jan-2005] $)

  $( Theorem *2.81 of [WhiteheadRussell] p. 108. $)
  pm2.81 $p |- ( ( ps -> ( ch -> th ) ) -> ( ( ph \/ ps ) ->
                ( ( ph \/ ch ) -> ( ph \/ th ) ) ) ) $=
    ( wi wo orim2 pm2.76 syl6 ) BCDEZEABFAJFACFADFEABJGACDHI $.
    $( [3-Jan-2005] $)

  $( Theorem *2.82 of [WhiteheadRussell] p. 108. $)
  pm2.82 $p |- ( ( ( ph \/ ps ) \/ ch ) -> ( ( ( ph \/ -. ch ) \/ th ) ->
                ( ( ph \/ ps ) \/ th ) ) ) $=
    ( wo wn wi ax-1 pm2.24 orim2d jaoi orim1d ) ABEZCEACFZEZMDMOMGCMOHCNBACBIJK
    L $.
    $( [3-Jan-2005] $)

  $( Theorem *2.85 of [WhiteheadRussell] p. 108.  (The proof was shortened by
     Wolf Lammen, 5-Jan-2013.) $)
  pm2.85 $p |- ( ( ( ph \/ ps ) -> ( ph \/ ch ) ) ->
                ( ph \/ ( ps -> ch ) ) ) $=
    ( wi wo orimdi biimpri ) ABCDEABEACEDABCFG $.
    $( [5-Jan-2013] $) $( [3-Jan-2005] $)

  ${
    pm3.2ni.1 $e |- -. ph $.
    pm3.2ni.2 $e |- -. ps $.
    $( Infer negated disjunction of negated premises. $)
    pm3.2ni $p |- -. ( ph \/ ps ) $=
      ( wo id pm2.21i jaoi mto ) ABEACAABAFBADGHI $.
      $( [4-Apr-1995] $)
  $}

  $( Absorption of redundant internal disjunct.  Compare Theorem *4.45 of
     [WhiteheadRussell] p. 119.  (The proof was shortened by Wolf Lammen,
     28-Feb-2014.) $)
  orabs $p |- ( ph <-> ( ( ph \/ ps ) /\ ph ) ) $=
    ( wo orc pm4.71ri ) AABCABDE $.
    $( [28-Feb-2014] $) $( [5-Aug-1993] $)

  $( Obsolete proof of ~ orabs as of 28-Feb-2014. $)
  orabsOLD $p |- ( ph <-> ( ( ph \/ ps ) /\ ph ) ) $=
    ( wo wa orc ancri simpr impbii ) AABCZADAIABEFIAGH $.
    $( [5-Aug-1993] $)

  $( Absorb a disjunct into a conjunct.  (Contributed by Roy F. Longton
     23-Jun-2005.)  (The proof was shortened by Wolf Lammen, 10-Nov-2013.) $)
  oranabs $p |- ( ( ( ph \/ -. ps ) /\ ps ) <-> ( ph /\ ps ) ) $=
    ( wn wo biortn orcom syl6rbb pm5.32ri ) BABCZDZABAIADJBAEIAFGH $.
    $( [10-Nov-2013] $) $( [23-Jun-2005] $)

  $( Two propositions are equivalent if they are both true.  Theorem *5.1 of
     [WhiteheadRussell] p. 123. $)
  pm5.1 $p |- ( ( ph /\ ps ) -> ( ph <-> ps ) ) $=
    ( wb pm5.501 biimpa ) ABABCABDE $.
    $( [21-May-1994] $)

  $( Two propositions are equivalent if they are both false.  Theorem *5.21 of
     [WhiteheadRussell] p. 124. $)
  pm5.21 $p |- ( ( -. ph /\ -. ps ) -> ( ph <-> ps ) ) $=
    ( wn wb pm5.21im imp ) ACBCABDABEF $.
    $( [19-May-2013] $) $( [21-May-1994] $)

  $( Theorem *3.43 (Comp) of [WhiteheadRussell] p. 113. $)
  pm3.43 $p |- ( ( ( ph -> ps ) /\ ( ph -> ch ) ) ->
                ( ph -> ( ps /\ ch ) ) ) $=
    ( wi wa pm3.43i imp ) ABDACDABCEDABCFG $.
    $( [27-Nov-2013] $) $( [3-Jan-2005] $)

  $( Distributive law for implication over conjunction.  Compare Theorem *4.76
     of [WhiteheadRussell] p. 121.  (The proof was shortened by Wolf Lammen,
     27-Nov-2013.) $)
  jcab $p |- ( ( ph -> ( ps /\ ch ) ) <->
                ( ( ph -> ps ) /\ ( ph -> ch ) ) ) $=
    ( wa wi simpl imim2i simpr jca pm3.43 impbii ) ABCDZEZABEZACEZDMNOLBABCFGLC
    ABCHGIABCJK $.
    $( [27-Nov-2013] $) $( [3-Apr-1994] $)

  $( Distributive law for disjunction.  Theorem *4.41 of [WhiteheadRussell]
     p. 119.  (The proof was shortened by Andrew Salmon, 7-May-2011.)  (The
     proof was shortened by Wolf Lammen, 28-Nov-2013.) $)
  ordi $p |- ( ( ph \/ ( ps /\ ch ) ) <-> ( ( ph \/ ps ) /\ ( ph \/ ch ) ) ) $=
    ( wn wa wi wo jcab df-or anbi12i 3bitr4i ) ADZBCEZFLBFZLCFZEAMGABGZACGZELBC
    HAMIPNQOABIACIJK $.
    $( [28-Nov-2013] $) $( [5-Aug-1993] $)

  $( Distributive law for disjunction. $)
  ordir $p |- ( ( ( ph /\ ps ) \/ ch ) <->
              ( ( ph \/ ch ) /\ ( ps \/ ch ) ) ) $=
    ( wa wo ordi orcom anbi12i 3bitr4i ) CABDZECAEZCBEZDJCEACEZBCEZDCABFJCGMKNL
    ACGBCGHI $.
    $( [12-Aug-1994] $)

  $( Obsolete proof of ~ jcab as of 27-Nov-2013 $)
  jcabOLD $p |- ( ( ph -> ( ps /\ ch ) ) <->
                 ( ( ph -> ps ) /\ ( ph -> ch ) ) ) $=
    ( wn wa wo wi ordi imor anbi12i 3bitr4i ) ADZBCEZFLBFZLCFZEAMGABGZACGZELBCH
    AMIPNQOABIACIJK $.
    $( [3-Apr-1994] $)

  $( Obsolete proof of ~ pm3.43 as of 27-Nov-2013 $)
  pm3.43OLD $p |- ( ( ( ph -> ps ) /\ ( ph -> ch ) ) ->
                ( ph -> ( ps /\ ch ) ) ) $=
    ( wa wi jcab biimpri ) ABCDEABEACEDABCFG $.
    $( [3-Jan-2005] $)

  $( Theorem *4.76 of [WhiteheadRussell] p. 121. $)
  pm4.76 $p |- ( ( ( ph -> ps ) /\ ( ph -> ch ) ) <->
                ( ph -> ( ps /\ ch ) ) ) $=
    ( wa wi jcab bicomi ) ABCDEABEACEDABCFG $.
    $( [3-Jan-2005] $)

  $( Distributive law for conjunction.  Theorem *4.4 of [WhiteheadRussell]
     p. 118.  (The proof was shortened by Wolf Lammen, 5-Jan-2013.) $)
  andi $p |- ( ( ph /\ ( ps \/ ch ) ) <-> ( ( ph /\ ps ) \/ ( ph /\ ch ) ) ) $=
    ( wo wa orc olc jaodan anim2i jaoi impbii ) ABCDZEZABEZACEZDZABPCNOFONGHNMO
    BLABCFICLACBGIJK $.
    $( [5-Jan-2013] $) $( [5-Aug-1993] $)

  $( Distributive law for conjunction. $)
  andir $p |- ( ( ( ph \/ ps ) /\ ch ) <->
              ( ( ph /\ ch ) \/ ( ps /\ ch ) ) ) $=
    ( wo wa andi ancom orbi12i 3bitr4i ) CABDZECAEZCBEZDJCEACEZBCEZDCABFJCGMKNL
    ACGBCGHI $.
    $( [12-Aug-1994] $)

  $( Double distributive law for disjunction. $)
  orddi $p |- ( ( ( ph /\ ps ) \/ ( ch /\ th ) ) <->
              ( ( ( ph \/ ch ) /\ ( ph \/ th ) ) /\
              ( ( ps \/ ch ) /\ ( ps \/ th ) ) ) ) $=
    ( wa wo ordir ordi anbi12i bitri ) ABECDEZFAKFZBKFZEACFADFEZBCFBDFEZEABKGLN
    MOACDHBCDHIJ $.
    $( [12-Aug-1994] $)

  $( Double distributive law for conjunction. $)
  anddi $p |- ( ( ( ph \/ ps ) /\ ( ch \/ th ) ) <->
              ( ( ( ph /\ ch ) \/ ( ph /\ th ) ) \/
              ( ( ps /\ ch ) \/ ( ps /\ th ) ) ) ) $=
    ( wo wa andir andi orbi12i bitri ) ABECDEZFAKFZBKFZEACFADFEZBCFBDFEZEABKGLN
    MOACDHBCDHIJ $.
    $( [12-Aug-1994] $)

  $( Prove formula-building rules for the biconditional connective. $)

  $( Theorem *4.39 of [WhiteheadRussell] p. 118. $)
  pm4.39 $p |- ( ( ( ph <-> ch ) /\ ( ps <-> th ) ) ->
                ( ( ph \/ ps ) <-> ( ch \/ th ) ) ) $=
    ( wb wa simpl simpr orbi12d ) ACEZBDEZFACBDJKGJKHI $.
    $( [3-Jan-2005] $)

  $( Theorem *4.38 of [WhiteheadRussell] p. 118. $)
  pm4.38 $p |- ( ( ( ph <-> ch ) /\ ( ps <-> th ) ) ->
                ( ( ph /\ ps ) <-> ( ch /\ th ) ) ) $=
    ( wb wa simpl simpr anbi12d ) ACEZBDEZFACBDJKGJKHI $.
    $( [3-Jan-2005] $)

  ${
    bi2an9.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    bi2an9.2 $e |- ( th -> ( ta <-> et ) ) $.
    $( Deduction joining two equivalences to form equivalence of
       conjunctions. $)
    bi2anan9 $p |- ( ( ph /\ th ) -> ( ( ps /\ ta ) <-> ( ch /\ et ) ) ) $=
      ( wa anbi1d anbi2d sylan9bb ) ABEICEIDCFIABCEGJDEFCHKL $.
      $( [31-Jul-1995] $)

    $( Deduction joining two equivalences to form equivalence of
       conjunctions. $)
    bi2anan9r $p |- ( ( th /\ ph ) -> ( ( ps /\ ta ) <-> ( ch /\ et ) ) ) $=
      ( wa wb bi2anan9 ancoms ) ADBEICFIJABCDEFGHKL $.
      $( [19-Feb-1996] $)

    $( Deduction joining two biconditionals with different antecedents. $)
    bi2bian9 $p |- ( ( ph /\ th ) -> ( ( ps <-> ta ) <-> ( ch <-> et ) ) ) $=
      ( wa wb adantr adantl bibi12d ) ADIBCEFABCJDGKDEFJAHLM $.
      $( [12-May-2004] $)
  $}

  $( Implication in terms of biconditional and disjunction.  Theorem *4.72 of
     [WhiteheadRussell] p. 121.  (The proof was shortened by Wolf Lammen,
     30-Jan-2013.) $)
  pm4.72 $p |- ( ( ph -> ps ) <-> ( ps <-> ( ph \/ ps ) ) ) $=
    ( wi wo wb olc pm2.621 impbid2 orc bi2 syl5 impbii ) ABCZBABDZEZMBNBAFABGHA
    NOBABIBNJKL $.
    $( [30-Jan-2013] $) $( [30-Aug-1993] $)

  $( Simplify an implication between implications.  (Contributed by Paul
     Chapman, 17-Nov-2012.)  (The proof was shortened by Wolf Lammen,
     3-Apr-2013.) $)
  imimorb $p |- ( ( ( ps -> ch ) -> ( ph -> ch ) ) <->
                  ( ph -> ( ps \/ ch ) ) ) $=
    ( wi wo bi2.04 dfor2 imbi2i bitr4i ) BCDZACDDAJCDZDABCEZDJACFLKABCGHI $.
    $( [3-Apr-2013] $) $( [17-Nov-2012] $)

  $( Theorem *5.33 of [WhiteheadRussell] p. 125. $)
  pm5.33 $p |- ( ( ph /\ ( ps -> ch ) ) <->
                ( ph /\ ( ( ph /\ ps ) -> ch ) ) ) $=
    ( wi wa ibar imbi1d pm5.32i ) ABCDABEZCDABICABFGH $.
    $( [3-Jan-2005] $)

  $( Theorem *5.36 of [WhiteheadRussell] p. 125. $)
  pm5.36 $p |- ( ( ph /\ ( ph <-> ps ) ) <-> ( ps /\ ( ph <-> ps ) ) ) $=
    ( wb id pm5.32ri ) ABCZABFDE $.
    $( [3-Jan-2005] $)

  ${
    bianabs.1 $e |- ( ph -> ( ps <-> ( ph /\ ch ) ) ) $.
    $( Absorb a hypothesis into the second member of a biconditional.
       (Contributed by FL, 15-Feb-2007.) $)
    bianabs $p |- ( ph -> ( ps <-> ch ) ) $=
      ( wa ibar bitr4d ) ABACECDACFG $.
      $( [22-May-2008] $) $( [15-Feb-2007] $)
  $}

  $( Absorption of disjunction into equivalence.  (The proof was shortened by
     Wolf Lammen, 3-Nov-2013.) $)
  oibabs $p |- ( ( ( ph \/ ps ) -> ( ph <-> ps ) ) <-> ( ph <-> ps ) ) $=
    ( wo wb wi wn wa ioran pm5.21 sylbi id ja ax-1 impbii ) ABCZABDZEPOPPOFAFBF
    GPABHABIJPKLPOMN $.
    $( [3-Nov-2013] $)  $( [6-Aug-1995] $)

  $( Law of noncontradiction.  Theorem *3.24 of [WhiteheadRussell] p. 111 (who
     call it the "law of contradiction").  (The proof was shortened by Wolf
     Lammen, 24-Nov-2012.) $)
  pm3.24 $p |- -. ( ph /\ -. ph ) $=
    ( wi wn wa id iman mpbi ) AABAACDCAEAAFG $.
    $( [24-Nov-2012] $) $( [16-Sep-1993] $)

  $( Theorem *2.26 of [WhiteheadRussell] p. 104.  (The proof was shortened by
     Wolf Lammen, 23-Nov-2012.) $)
  pm2.26 $p |- ( -. ph \/ ( ( ph -> ps ) -> ps ) ) $=
    ( wi pm2.27 imori ) AABCBCABDE $.
    $( [23-Nov-2012] $) $( [3-Jan-2005] $)

  $( Theorem *5.11 of [WhiteheadRussell] p. 123. $)
  pm5.11 $p |- ( ( ph -> ps ) \/ ( -. ph -> ps ) ) $=
    ( wi wn pm2.5 orri ) ABCADBCABEF $.
    $( [3-Jan-2005] $)

  $( Theorem *5.12 of [WhiteheadRussell] p. 123. $)
  pm5.12 $p |- ( ( ph -> ps ) \/ ( ph -> -. ps ) ) $=
    ( wi wn pm2.51 orri ) ABCABDCABEF $.
    $( [3-Jan-2005] $)

  $( Theorem *5.14 of [WhiteheadRussell] p. 123. $)
  pm5.14 $p |- ( ( ph -> ps ) \/ ( ps -> ch ) ) $=
    ( wi wn ax-1 con3i pm2.21d orri ) ABDZBCDJEBCBJBAFGHI $.
    $( [3-Jan-2005] $)

  $( Theorem *5.13 of [WhiteheadRussell] p. 123.  (The proof was shortened by
     Wolf Lammen, 14-Nov-2012.) $)
  pm5.13 $p |- ( ( ph -> ps ) \/ ( ps -> ph ) ) $=
    ( pm5.14 ) ABAC $.
    $( [14-Nov-2012] $) $( [3-Jan-2005] $)

  $( Theorem *5.17 of [WhiteheadRussell] p. 124.  (The proof was shortened by
     Wolf Lammen, 3-Jan-2013.) $)
  pm5.17 $p |- ( ( ( ph \/ ps ) /\ -. ( ph /\ ps ) ) <-> ( ph <-> -. ps ) ) $=
    ( wn wb wi wa wo bicom dfbi2 orcom df-or bitr2i imnan anbi12i 3bitrri ) ABC
    ZDPADPAEZAPEZFABGZABFCZFAPHPAIQSRTSBAGQABJBAKLABMNO $.
    $( [3-Jan-2013] $) $( [3-Jan-2005] $)

  $( Theorem *5.15 of [WhiteheadRussell] p. 124.  (The proof was shortened by
     Wolf Lammen, 15-Oct-2013.) $)
  pm5.15 $p |- ( ( ph <-> ps ) \/ ( ph <-> -. ps ) ) $=
    ( wb wn xor3 biimpi orri ) ABCZABDCZHDIABEFG $.
    $( [15-Oct-2013] $) $( [3-Jan-2005] $)

  $( Theorem *5.16 of [WhiteheadRussell] p. 124.  (The proof was shortened by
     Wolf Lammen, 17-Oct-2013.) $)
  pm5.16 $p |- -. ( ( ph <-> ps ) /\ ( ph <-> -. ps ) ) $=
    ( wb wn wi wa pm5.18 biimpi imnan mpbi ) ABCZABDCZDZEKLFDKMABGHKLIJ $.
    $( [17-Oct-2013] $) $( [3-Jan-2005] $)

  $( Two ways to express "exclusive or."  Theorem *5.22 of [WhiteheadRussell]
     p. 124.  (The proof was shortened by Wolf Lammen, 22-Jan-2013.) $)
  xor $p |- ( -. ( ph <-> ps ) <->
                ( ( ph /\ -. ps ) \/ ( ps /\ -. ph ) ) ) $=
    ( wn wa wo wb wi iman anbi12i dfbi2 ioran 3bitr4ri con1bii ) ABCDZBACDZEZAB
    FZABGZBAGZDNCZOCZDQPCRTSUAABHBAHIABJNOKLM $.
    $( [22-Jan-2013] $) $( [3-Jan-2005] $)

  $( Two ways to express "exclusive or."  (The proof was shortened by Wolf
     Lammen, 24-Jan-2013.) $)
  xor2 $p |- ( -. ( ph <-> ps ) <-> ( ( ph \/ ps ) /\ -. ( ph /\ ps ) ) ) $=
    ( wb wn wo wa xor3 pm5.17 bitr4i ) ABCDABDCABEABFDFABGABHI $.
    $( [24-Jan-2013] $) $( [3-Jan-2005] $)

  $( An alternate definition of the biconditional.  Theorem *5.23 of
     [WhiteheadRussell] p. 124.  (The proof was shortened by Wolf Lammen,
     3-Nov-2013.) $)
  dfbi3 $p |- ( ( ph <-> ps ) <-> ( ( ph /\ ps ) \/ ( -. ph /\ -. ps ) ) ) $=
    ( wn wb wa wo xor pm5.18 notnot anbi2i ancom orbi12i 3bitr4i ) ABCZDCANCZEZ
    NACZEZFABDABEZQNEZFANGABHSPTRBOABIJQNKLM $.
    $( [3-Nov-2013] $) $( [27-Jun-2002] $)

  $( Theorem *5.24 of [WhiteheadRussell] p. 124. $)
  pm5.24 $p |- ( -. ( ( ph /\ ps ) \/ ( -. ph /\ -. ps ) ) <->
                ( ( ph /\ -. ps ) \/ ( ps /\ -. ph ) ) ) $=
    ( wb wn wa wo xor dfbi3 xchnxbi ) ABCABDZEBADZEFABEKJEFABGABHI $.
    $( [3-Jan-2005] $)

  $( Conjunction distributes over exclusive-or, using ` -. ( ph <-> ps ) ` to
     express exclusive-or.  This is one way to interpret the distributive law
     of multiplication over addition in modulo 2 arithmetic. $)
  xordi $p |- ( ( ph /\ -. ( ps <-> ch ) ) <->
                -. ( ( ph /\ ps ) <-> ( ph /\ ch ) ) ) $=
    ( wb wn wa wi annim pm5.32 xchbinx ) ABCDZEFAKGABFACFDAKHABCIJ $.
    $( [3-Oct-2008] $)

  $( A wff is disjoined with truth is true. $)
  biort $p |- ( ph -> ( ph <-> ( ph \/ ps ) ) ) $=
    ( wo orc ax-1 impbid2 ) AAABCZABDAGEF $.
    $( [23-May-1999] $)

  $( Theorem *5.55 of [WhiteheadRussell] p. 125.  (The proof was shortened by
     Wolf Lammen, 20-Jan-2013.) $)
  pm5.55 $p |- ( ( ( ph \/ ps ) <-> ph ) \/ ( ( ph \/ ps ) <-> ps ) ) $=
    ( wo wb biort bicomd wn biorf nsyl4 con1i orri ) ABCZADZLBDZNMAMNAALABEFAGB
    LABHFIJK $.
    $( [20-Jan-2013] $) $( [3-Jan-2005] $)

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Miscellaneous theorems of propositional calculus
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    pm5.21nd.1 $e |- ( ( ph /\ ps ) -> th ) $.
    pm5.21nd.2 $e |- ( ( ph /\ ch ) -> th ) $.
    pm5.21nd.3 $e |- ( th -> ( ps <-> ch ) ) $.
    $( Eliminate an antecedent implied by each side of a biconditional.  (The
       proof was shortened by Wolf Lammen, 4-Nov-2013.) $)
    pm5.21nd $p |- ( ph -> ( ps <-> ch ) ) $=
      ( ex wb wi a1i pm5.21ndd ) ADBCABDEHACDFHDBCIJAGKL $.
      $( [4-Nov-2013] $) $( [20-Nov-2005] $)
  $}

  $( Theorem *5.35 of [WhiteheadRussell] p. 125. $)
  pm5.35 $p |- ( ( ( ph -> ps ) /\ ( ph -> ch ) ) ->
                ( ph -> ( ps <-> ch ) ) ) $=
    ( wi wa pm5.1 pm5.74rd ) ABDZACDZEABCHIFG $.
    $( [3-Jan-2005] $)

  $( Theorem *5.54 of [WhiteheadRussell] p. 125.  (The proof was shortened by
     Wolf Lammen, 7-Nov-2013.) $)
  pm5.54 $p |- ( ( ( ph /\ ps ) <-> ph ) \/ ( ( ph /\ ps ) <-> ps ) ) $=
    ( wa wb iba bicomd adantl pm5.21ni orri ) ABCZADZJBDJKBBKABAJBAEFZGLHI $.
    $( [7-Nov-2013] $) $( [3-Jan-2005] $)

  ${
    baib.1 $e |- ( ph <-> ( ps /\ ch ) ) $.
    $( Move conjunction outside of biconditional. $)
    baib $p |- ( ps -> ( ph <-> ch ) ) $=
      ( wa ibar syl6rbbr ) BCBCEABCFDG $.
      $( [13-May-1999] $)
  $}

  ${
    baibr.1 $e |- ( ph <-> ( ps /\ ch ) ) $.
    $( Move conjunction outside of biconditional. $)
    baibr $p |- ( ps -> ( ch <-> ph ) ) $=
      ( baib bicomd ) BACABCDEF $.
      $( [11-Jul-1994] $)
  $}

  $( Theorem *5.44 of [WhiteheadRussell] p. 125. $)
  pm5.44 $p |- ( ( ph -> ps ) -> ( ( ph -> ch ) <->
                ( ph -> ( ps /\ ch ) ) ) ) $=
    ( wa wi jcab baibr ) ABCDEABEACEABCFG $.
    $( [3-Jan-2005] $)

  $( Conjunction in antecedent versus disjunction in consequent.  Theorem *5.6
     of [WhiteheadRussell] p. 125. $)
  pm5.6 $p |- ( ( ( ph /\ -. ps ) -> ch ) <-> ( ph -> ( ps \/ ch ) ) ) $=
    ( wn wa wi wo impexp df-or imbi2i bitr4i ) ABDZECFALCFZFABCGZFALCHNMABCIJK
    $.
    $( [22-Mar-2005] $) $( [8-Jun-1994] $)

  ${
    orcanai.1 $e |- ( ph -> ( ps \/ ch ) ) $.
    $( Change disjunction in consequent to conjunction in antecedent. $)
    orcanai $p |- ( ( ph /\ -. ps ) -> ch ) $=
      ( wn ord imp ) ABECABCDFG $.
      $( [8-Jun-1994] $)
  $}


  ${
    intnan.1 $e |- -. ph $.
    $( Introduction of conjunct inside of a contradiction. $)
    intnan $p |- -. ( ps /\ ph ) $=
      ( wa simpr mto ) BADACBAEF $.
      $( [16-Sep-1993] $)

    $( Introduction of conjunct inside of a contradiction. $)
    intnanr $p |- -. ( ph /\ ps ) $=
      ( wa simpl mto ) ABDACABEF $.
      $( [3-Apr-1995] $)
  $}

  ${
    intnand.1 $e |- ( ph -> -. ps ) $.
    $( Introduction of conjunct inside of a contradiction. $)
    intnand $p |- ( ph -> -. ( ch /\ ps ) ) $=
      ( wa simpr nsyl ) ABCBEDCBFG $.
      $( [10-Jul-2005] $)

    $( Introduction of conjunct inside of a contradiction. $)
    intnanrd $p |- ( ph -> -. ( ps /\ ch ) ) $=
      ( wa simpl nsyl ) ABBCEDBCFG $.
      $( [10-Jul-2005] $)
  $}

  ${
    mpbiran.1 $e |- ps $.
    mpbiran.2 $e |- ( ph <-> ( ps /\ ch ) ) $.
    $( Detach truth from conjunction in biconditional. $)
    mpbiran $p |- ( ph <-> ch ) $=
      ( wa biantrur bitr4i ) ABCFCEBCDGH $.
      $( [9-Jan-2015] $) $( [27-Feb-1996] $)
  $}

  ${
    mpbiran2.1 $e |- ch $.
    mpbiran2.2 $e |- ( ph <-> ( ps /\ ch ) ) $.
    $( Detach truth from conjunction in biconditional. $)
    mpbiran2 $p |- ( ph <-> ps ) $=
      ( wa biantru bitr4i ) ABCFBECBDGH $.
      $( [9-Jan-2015] $) $( [22-Feb-1996] $)
  $}

  ${
    mpbir2an.1 $e |- ps $.
    mpbir2an.2 $e |- ch $.
    mpbiran2an.1 $e |- ( ph <-> ( ps /\ ch ) ) $.
    $( Detach a conjunction of truths in a biconditional. $)
    mpbir2an $p |- ph $=
      ( mpbiran mpbir ) ACEABCDFGH $.
      $( [9-Jan-2015] $) $( [10-May-2005] $)
  $}

  ${
    mpbi2and.1 $e |- ( ph -> ps ) $.
    mpbi2and.2 $e |- ( ph -> ch ) $.
    mpbi2and.3 $e |- ( ph -> ( ( ps /\ ch ) <-> th ) ) $.
    $( Detach a conjunction of truths in a biconditional.  (The proof was
       shortened by Wolf Lammen, 24-Nov-2012.) $)
    mpbi2and $p |- ( ph -> th ) $=
      ( wa jca mpbid ) ABCHDABCEFIGJ $.
      $( [9-Jan-2015] $) $( [6-Nov-2011] $)
  $}

  ${
    mpbir2and.1 $e |- ( ph -> ch ) $.
    mpbir2and.2 $e |- ( ph -> th ) $.
    mpbir2and.3 $e |- ( ph -> ( ps <-> ( ch /\ th ) ) ) $.
    $( Detach a conjunction of truths in a biconditional.  (The proof was
       shortened by Wolf Lammen, 24-Nov-2012.) $)
    mpbir2and $p |- ( ph -> ps ) $=
      ( wa jca mpbird ) ABCDHACDEFIGJ $.
      $( [9-Jan-2015] $)  $( [6-Nov-2011] $)
  $}

  ${
    mpbiranOLD.1 $e |- ( ph <-> ( ps /\ ch ) ) $.
    ${
      mpbiranOLD.2 $e |- ps $.
      $( Obsolete version of ~ mpbiran as of 9-Jan-2015. $)
      mpbiranOLD $p |- ( ph <-> ch ) $=
        ( mpbiran ) ABCEDF $.
        $( [27-Feb-1996] $)
    $}

    ${
      mpbiran2OLD.2 $e |- ch $.
      $( Obsolete version of ~ mpbiran2 as of 9-Jan-2015. $)
      mpbiran2OLD $p |- ( ph <-> ps ) $=
        ( mpbiran2 ) ABCEDF $.
        $( [22-Feb-1996] $)
    $}

    ${
      mpbir2anOLD.2 $e |- ps $.
      mpbir2anOLD.3 $e |- ch $.
      $( Obsolete version of ~ mpbir2an as of 9-Jan-2015. $)
      mpbir2anOLD $p |- ph $=
        ( mpbir2an ) ABCEFDG $.
        $( [10-May-2005] $)
    $}
  $}

  ${
    mpbi2andOLD.1 $e |- ( ph -> ( ( ps /\ ch ) <-> th ) ) $.
    mpbi2andOLD.2 $e |- ( ph -> ps ) $.
    mpbi2andOLD.3 $e |- ( ph -> ch ) $.
    $( Obsolete version of ~ mpbi2and as of 9-Jan-2015. $)
    mpbi2andOLD $p |- ( ph -> th ) $=
      ( mpbi2and ) ABCDFGEH $.
      $( [24-Nov-2012] $) $( [6-Nov-2011] $)
  $}

  ${
    mpbir2andOLD.1 $e |- ( ph -> ( ps <-> ( ch /\ th ) ) ) $.
    mpbir2andOLD.2 $e |- ( ph -> ch ) $.
    mpbir2andOLD.3 $e |- ( ph -> th ) $.
    $( Obsolete version of ~ mpbir2and as of 9-Jan-2015. $)
    mpbir2andOLD $p |- ( ph -> ps ) $=
      ( mpbir2and ) ABCDFGEH $.
      $( [24-Nov-2012] $) $( [6-Nov-2011] $)
  $}

  $( Theorem *5.62 of [WhiteheadRussell] p. 125.  (Contributed by Roy F.
     Longton, 21-Jun-2005.) $)
  pm5.62 $p |- ( ( ( ph /\ ps ) \/ -. ps ) <-> ( ph \/ -. ps ) ) $=
    ( wa wn wo exmid ordir mpbiran2 ) ABCBDZEAIEBIEBFABIGH $.
    $( [21-Jun-2005] $)

  $( Theorem *5.63 of [WhiteheadRussell] p. 125.  (The proof was shortened by
     Wolf Lammen, 25-Dec-2012.) $)
  pm5.63 $p |- ( ( ph \/ ps ) <-> ( ph \/ ( -. ph /\ ps ) ) ) $=
    ( wn wa wo exmid ordi mpbiran bicomi ) AACZBDEZABEZKAJELAFAJBGHI $.
    $( [25-Dec-2012] $) $( [3-Jan-2005] $)

  ${
    bianfi.1 $e |- -. ph $.
    $( A wff conjoined with falsehood is false.  (The proof was shortened by
       Wolf Lammen, 26-Nov-2012.) $)
    bianfi $p |- ( ph <-> ( ps /\ ph ) ) $=
      ( wa intnan 2false ) ABADCABCEF $.
      $( [26-Nov-2012] $) $( [5-Aug-1993] $)
  $}

  ${
    bianfd.1 $e |- ( ph -> -. ps ) $.
    $( A wff conjoined with falsehood is false.  (The proof was shortened by
       Wolf Lammen, 5-Nov-2013.) $)
    bianfd $p |- ( ph -> ( ps <-> ( ps /\ ch ) ) ) $=
      ( wa intnanrd 2falsed ) ABBCEDABCDFG $.
      $( [5-Nov-2013] $) $( [27-Mar-1995] $)
  $}

  $( Theorem *4.43 of [WhiteheadRussell] p. 119.  (The proof was shortened by
     Wolf Lammen, 26-Nov-2012.) $)
  pm4.43 $p |- ( ph <-> ( ( ph \/ ps ) /\ ( ph \/ -. ps ) ) ) $=
    ( wn wa wo pm3.24 biorfi ordi bitri ) AABBCZDZEABEAJEDKABFGABJHI $.
    $( [26-Nov-2012] $) $( [3-Jan-2005] $)

  $( Theorem *4.82 of [WhiteheadRussell] p. 122. $)
  pm4.82 $p |- ( ( ( ph -> ps ) /\ ( ph -> -. ps ) ) <-> -. ph ) $=
    ( wi wn wa pm2.65 imp pm2.21 jca impbii ) ABCZABDZCZEADZKMNABFGNKMABHALHIJ
    $.
    $( [3-Jan-2005] $)

  $( Theorem *4.83 of [WhiteheadRussell] p. 122. $)
  pm4.83 $p |- ( ( ( ph -> ps ) /\ ( -. ph -> ps ) ) <-> ps ) $=
    ( wn wo wi wa exmid a1bi jaob bitr2i ) BAACZDZBEABEKBEFLBAGHABKIJ $.
    $( [3-Jan-2005] $)

  $( Negation inferred from embedded conjunct.  (The proof was shortened by
     Wolf Lammen, 25-Nov-2012.) $)
  pclem6 $p |- ( ( ph <-> ( ps /\ -. ph ) ) -> -. ps ) $=
    ( wn wa wb ibar nbbn sylib con2i ) BABACZDZEZBJKELCBJFAKGHI $.
    $( [25-Nov-2012] $) $( [20-Aug-1993] $)

  $( A transitive law of equivalence.  Compare Theorem *4.22 of
     [WhiteheadRussell] p. 117. $)
  biantr $p |- ( ( ( ph <-> ps ) /\ ( ch <-> ps ) ) -> ( ph <-> ch ) ) $=
    ( wb id bibi2d biimparc ) CBDZACDABDHCBAHEFG $.
    $( [18-Aug-1993] $)

  $( Disjunction distributes over the biconditional.  An axiom of system DS in
     Vladimir Lifschitz, "On calculational proofs" (1998),
     ~ http://citeseerx.ist.psu.edu/viewdoc/summary?doi=10.1.1.25.3384 .  (The
     proof was shortened by Wolf Lammen, 4-Feb-2013.) $)
  orbidi $p |- ( ( ph \/ ( ps <-> ch ) ) <->
                ( ( ph \/ ps ) <-> ( ph \/ ch ) ) ) $=
    ( wn wb wi wo pm5.74 df-or bibi12i 3bitr4i ) ADZBCEZFLBFZLCFZEAMGABGZACGZEL
    BCHAMIPNQOABIACIJK $.
    $( [4-Feb-2013] $) $( [8-Jan-2005] $)

  $( Lukasiewicz's shortest axiom for equivalential calculus.  Storrs McCall,
     ed., _Polish Logic 1920-1939_ (Oxford, 1967), p. 96. $)
  biluk $p |- ( ( ph <-> ps ) <-> ( ( ch <-> ps ) <-> ( ph <-> ch ) ) ) $=
    ( wb bicom bibi1i biass bitri mpbi bitr4i ) ABDZCBACDZDZDZCBDLDKCDZMDKNDOBA
    DZCDMKPCABEFBACGHKCMGICBLGJ $.
    $( [10-Jan-2005] $)

  $( Disjunction distributes over the biconditional.  Theorem *5.7 of
     [WhiteheadRussell] p. 125.  This theorem is similar to ~ orbidi .
     (Contributed by Roy F. Longton, 21-Jun-2005.) $)
  pm5.7 $p |- ( ( ( ph \/ ch ) <-> ( ps \/ ch ) ) <->
               ( ch \/ ( ph <-> ps ) ) ) $=
    ( wb wo orbidi orcom bibi12i bitr2i ) CABDECAEZCBEZDACEZBCEZDCABFJLKMCAGCBG
    HI $.
    $( [21-Jun-2005] $)

  $( Dijkstra-Scholten's Golden Rule for calculational proofs. $)
  bigolden $p |- ( ( ( ph /\ ps ) <-> ph ) <-> ( ps <-> ( ph \/ ps ) ) ) $=
    ( wi wa wb wo pm4.71 pm4.72 bicom 3bitr3ri ) ABCAABDZEBABFEKAEABGABHAKIJ $.
    $( [10-Jan-2005] $)

  $( Theorem *5.71 of [WhiteheadRussell] p. 125.  (Contributed by Roy F.
     Longton, 23-Jun-2005.) $)
  pm5.71 $p |- ( ( ps -> -. ch ) -> ( ( ( ph \/ ps ) /\ ch ) <->
                ( ph /\ ch ) ) ) $=
    ( wn wo wa wb orel2 orc impbid1 anbi1d pm2.21 pm5.32rd ja ) BCDZABEZCFACFGB
    DZPACQPABAHABIJKOCPACPAGLMN $.
    $( [23-Jun-2005] $)

  $( Theorem *5.75 of [WhiteheadRussell] p. 126.  (The proof was shortened by
     Andrew Salmon, 7-May-2011.)  (The proof was shortened by Wolf Lammen,
     23-Dec-2012.) $)
  pm5.75 $p |- ( ( ( ch -> -. ps ) /\ ( ph <-> ( ps \/ ch ) ) ) ->
                ( ( ph /\ -. ps ) <-> ch ) ) $=
    ( wo wb wn wa wi anbi1 anbi1i pm5.61 syl6bb pm4.71 biimpi bicomd sylan9bbr
    orcom bitri ) ABCDZEZABFZGZCUAGZCUAHZCTUBSUAGZUCASUAIUECBDZUAGUCSUFUABCQJCB
    KRLUDCUCUDCUCECUAMNOP $.
    $( [23-Dec-2012] $) $( [3-Jan-2005] $)

  $( Removal of conjunct from one side of an equivalence. $)
  bimsc1 $p |- ( ( ( ph -> ps ) /\ ( ch <-> ( ps /\ ph ) ) )
               -> ( ch <-> ph ) ) $=
    ( wi wa wb simpr ancr impbid2 bibi2d biimpa ) ABDZCBAEZFCAFLMACLMABAGABHIJK
    $.
    $( [5-Aug-1993] $)

  $( The disjunction of the four possible combinations of two wffs and their
     negations is always true.  (Contributed by David Abernethy,
     28-Jan-2014.) $)
  4exmid $p |- ( ( ( ph /\ ps ) \/ ( -. ph /\ -. ps ) )
              \/ ( ( ph /\ -. ps ) \/ ( ps /\ -. ph ) ) ) $=
    ( wb wn wo wa exmid dfbi3 xor orbi12i mpbi ) ABCZLDZEABFADZBDZFEZAOFBNFEZEL
    GLPMQABHABIJK $.
    $( [1-Feb-2014] $)

  ${
    ecase2d.1 $e |- ( ph -> ps ) $.
    ecase2d.2 $e |- ( ph -> -. ( ps /\ ch ) ) $.
    ecase2d.3 $e |- ( ph -> -. ( ps /\ th ) ) $.
    ecase2d.4 $e |- ( ph -> ( ta \/ ( ch \/ th ) ) ) $.
    $( Deduction for elimination by cases.  (The proof was shortened by Wolf
       Lammen, 22-Dec-2012.) $)
    ecase2d $p |- ( ph -> ta ) $=
      ( wo wn wa wi imnan sylibr mpd ioran sylanbrc ord mt3d ) AECDJZACKZDKZUAK
      ABUBFABCLKBUBMGBCNOPABUCFABDLKBUCMHBDNOPCDQRAEUAIST $.
      $( [22-Dec-2012] $) $( [21-Apr-1994] $)
  $}

  ${
    ecase3.1 $e |- ( ph -> ch ) $.
    ecase3.2 $e |- ( ps -> ch ) $.
    ecase3.3 $e |- ( -. ( ph \/ ps ) -> ch ) $.
    $( Inference for elimination by cases.  (The proof was shortened by Wolf
       Lammen, 26-Nov-2012.) $)
    ecase3 $p |- ch $=
      ( wo jaoi pm2.61i ) ABGCACBDEHFI $.
      $( [26-Nov-2012] $) $( [23-Mar-1995] $)
  $}

  ${
    ecase.1 $e |- ( -. ph -> ch ) $.
    ecase.2 $e |- ( -. ps -> ch ) $.
    ecase.3 $e |- ( ( ph /\ ps ) -> ch ) $.
    $( Inference for elimination by cases. $)
    ecase $p |- ch $=
      ( ex pm2.61nii ) ABCABCFGDEH $.
      $( [13-Jul-2005] $)
  $}

  ${
    ecase3d.1 $e |- ( ph -> ( ps -> th ) ) $.
    ecase3d.2 $e |- ( ph -> ( ch -> th ) ) $.
    ecase3d.3 $e |- ( ph -> ( -. ( ps \/ ch ) -> th ) ) $.
    $( Deduction for elimination by cases.  (The proof was shortened by Andrew
       Salmon, 7-May-2011.) $)
    ecase3d $p |- ( ph -> th ) $=
      ( wo jaod pm2.61d ) ABCHDABDCEFIGJ $.
      $( [12-May-2011] $) $( [2-May-1996] $)
  $}

  ${
    ecased.1 $e |- ( ph -> ( -. ps -> th ) ) $.
    ecased.2 $e |- ( ph -> ( -. ch -> th ) ) $.
    ecased.3 $e |- ( ph -> ( ( ps /\ ch ) -> th ) ) $.
    $( Deduction for elimination by cases. $)
    ecased $p |- ( ph -> th ) $=
      ( wn wo wa pm3.11 syl5 ecase3d ) ABHZCHZDEFNOIHBCJADBCKGLM $.
      $( [8-Oct-2012] $)
  $}

  ${
    ecase3ad.1 $e |- ( ph -> ( ps -> th ) ) $.
    ecase3ad.2 $e |- ( ph -> ( ch -> th ) ) $.
    ecase3ad.3 $e |- ( ph -> ( ( -. ps /\ -. ch ) -> th ) ) $.
    $( Deduction for elimination by cases. $)
    ecase3ad $p |- ( ph -> th ) $=
      ( wn notnot2 syl5 ecased ) ABHZCHZDLHBADBIEJMHCADCIFJGK $.
      $( [24-May-2013] $)
  $}

  ${
    ccase.1 $e |- ( ( ph /\ ps ) -> ta ) $.
    ccase.2 $e |- ( ( ch /\ ps ) -> ta ) $.
    ccase.3 $e |- ( ( ph /\ th ) -> ta ) $.
    ccase.4 $e |- ( ( ch /\ th ) -> ta ) $.
    $( Inference for combining cases.  (The proof was shortened by Wolf Lammen,
       6-Jan-2013.) $)
    ccase $p |- ( ( ( ph \/ ch ) /\ ( ps \/ th ) ) -> ta ) $=
      ( wo jaoian jaodan ) ACJBEDABECFGKADECHIKL $.
      $( [6-Jan-2013] $) $( [29-Jul-1999] $)
  $}

  ${
    ccased.1 $e |- ( ph -> ( ( ps /\ ch ) -> et ) ) $.
    ccased.2 $e |- ( ph -> ( ( th /\ ch ) -> et ) ) $.
    ccased.3 $e |- ( ph -> ( ( ps /\ ta ) -> et ) ) $.
    ccased.4 $e |- ( ph -> ( ( th /\ ta ) -> et ) ) $.
    $( Deduction for combining cases. $)
    ccased $p |- ( ph -> ( ( ( ps \/ th ) /\ ( ch \/ ta ) ) -> et ) ) $=
      ( wo wa wi com12 ccase ) BDKCEKLAFBCDEAFMABCLFGNADCLFHNABELFINADELFJNON
      $.
      $( [9-May-2004] $)
  $}

  ${
    ccase2.1 $e |- ( ( ph /\ ps ) -> ta ) $.
    ccase2.2 $e |- ( ch -> ta ) $.
    ccase2.3 $e |- ( th -> ta ) $.
    $( Inference for combining cases. $)
    ccase2 $p |- ( ( ( ph \/ ch ) /\ ( ps \/ th ) ) -> ta ) $=
      ( adantr adantl ccase ) ABCDEFCEBGIDEAHJDECHJK $.
      $( [29-Jul-1999] $)
  $}

  ${
    4cases.1 $e |- ( ( ph /\ ps ) -> ch ) $.
    4cases.2 $e |- ( ( ph /\ -. ps ) -> ch ) $.
    4cases.3 $e |- ( ( -. ph /\ ps ) -> ch ) $.
    4cases.4 $e |- ( ( -. ph /\ -. ps ) -> ch ) $.
    $( Inference eliminating two antecedents from the four possible cases that
       result from their true/false combinations. $)
    4cases $p |- ch $=
      ( pm2.61ian wn pm2.61i ) BCABCDFHABICEGHJ $.
      $( [25-Oct-2003] $)
  $}

  ${
    4casesdan.1 $e |- ( ( ph /\ ( ps /\ ch ) ) -> th ) $.
    4casesdan.2 $e |- ( ( ph /\ ( ps /\ -. ch ) ) -> th ) $.
    4casesdan.3 $e |- ( ( ph /\ ( -. ps /\ ch ) ) -> th ) $.
    4casesdan.4 $e |- ( ( ph /\ ( -. ps /\ -. ch ) ) -> th ) $.
    $( Deduction eliminating two antecedents from the four possible cases that
       result from their true/false combinations. $)
    4casesdan $p |- ( ph -> th ) $=
      ( wi wa expcom wn 4cases ) BCADIABCJDEKABCLZJDFKABLZCJDGKAONJDHKM $.
      $( [19-Mar-2013] $)
  $}

  ${
    niabn.1 $e |- ph $.
    $( Miscellaneous inference relating falsehoods. $)
    niabn $p |- ( -. ps -> ( ( ch /\ ps ) <-> -. ph ) ) $=
      ( wa wn simpr pm2.24i pm5.21ni ) CBEBAFCBGABDHI $.
      $( [31-Mar-1994] $)
  $}

  $( Lemma for an alternate version of weak deduction theorem.  (The proof was
     shortened by Andrew Salmon, 7-May-2011.)  (The proof was shortened by Wolf
     Lammen, 4-Dec-2012.) $)
  dedlem0a $p |- ( ph -> ( ps <-> ( ( ch -> ph ) -> ( ps /\ ph ) ) ) ) $=
    ( wa wi iba wb ax-1 biimt syl bitrd ) ABBADZCAEZLEZABFAMLNGACHMLIJK $.
    $( [4-Dec-2012] $) $( [2-Apr-1994] $)

  $( Lemma for an alternate version of weak deduction theorem. $)
  dedlem0b $p |- ( -. ph -> ( ps <-> ( ( ps -> ph ) -> ( ch /\ ph ) ) ) ) $=
    ( wn wi wa pm2.21 imim2d com23 simpr imim12i con1d com12 impbid ) ADZBBAEZC
    AFZEZOPBQOAQBAQGHIROBRBABDPQABAGCAJKLMN $.
    $( [2-Apr-1994] $)

  $( Lemma for weak deduction theorem.  (The proof was shortened by Andrew
     Salmon, 7-May-2011.) $)
  dedlema $p |- ( ph -> ( ps <-> ( ( ps /\ ph ) \/ ( ch /\ -. ph ) ) ) ) $=
    ( wa wn wo orc expcom wi simpl a1i pm2.24 adantld jaod impbid ) ABBADZCAEZD
    ZFZBASPRGHAPBRPBIABAJKAQBCABLMNO $.
    $( [12-May-2011] $) $( [26-Jun-2002] $)

  $( Lemma for weak deduction theorem.  (The proof was shortened by Andrew
     Salmon, 7-May-2011.) $)
  dedlemb $p |- ( -. ph -> ( ch <-> ( ( ps /\ ph ) \/ ( ch /\ -. ph ) ) ) ) $=
    ( wn wa wo olc expcom pm2.21 adantld wi simpl a1i jaod impbid ) ADZCBAEZCPE
    ZFZCPSRQGHPQCRPACBACIJRCKPCPLMNO $.
    $( [12-May-2011] $) $( [15-May-1999] $)

  ${
    elimh.1 $e |- ( ( ph <-> ( ( ph /\ ch ) \/ ( ps /\ -. ch ) ) )
                     -> ( ch <-> ta ) ) $.
    elimh.2 $e |- ( ( ps <-> ( ( ph /\ ch ) \/ ( ps /\ -. ch ) ) )
                     -> ( th <-> ta ) ) $.
    elimh.3 $e |- th $.
    $( Hypothesis builder for weak deduction theorem.  For more information,
       see the Deduction Theorem link on the Metamath Proof Explorer home
       page. $)
    elimh $p |- ta $=
      ( wa wn wo wb dedlema syl ibi dedlemb mpbii pm2.61i ) CECECAACIBCJZIKZLCE
      LCABMFNOSDEHSBTLDELCABPGNQR $.
      $( [26-Jun-2002] $)
  $}

  ${
    dedt.1 $e |- ( ( ph <-> ( ( ph /\ ch ) \/ ( ps /\ -. ch ) ) )
                     -> ( th <-> ta ) ) $.
    dedt.2 $e |- ta $.
    $( The weak deduction theorem.  For more information, see the Deduction
       Theorem link on the Metamath Proof Explorer home page. $)
    dedt $p |- ( ch -> th ) $=
      ( wa wn wo wb dedlema mpbiri syl ) CAACHBCIHJKZDCABLODEGFMN $.
      $( [26-Jun-2002] $)
  $}

  $( Contraposition.  Theorem *2.16 of [WhiteheadRussell] p. 103.  This version
     of ~ con3 demonstrates the use of the weak deduction theorem to derive it
     from ~ con3i . $)
  con3th $p |- ( ( ph -> ps ) -> ( -. ps -> -. ph ) ) $=
    ( wi wn wa wo wb id notbid imbi1d imbi2d elimh con3i dedt ) BAABCZBDZADZCBO
    EAODEFZDZQCBRGZPSQTBRTHZIJARBAOAACARCTBRAUAKARGZARAUBHKAHLMN $.
    $( [27-Jun-2002] $)

  $( The consensus theorem.  This theorem and its dual (with ` \/ ` and ` /\ `
     interchanged) are commonly used in computer logic design to eliminate
     redundant terms from Boolean expressions.  Specifically, we prove that the
     term ` ( ps /\ ch ) ` on the left-hand side is redundant.  (The proof was
     shortened by Andrew Salmon, 13-May-2011.)  (The proof was shortened by
     Wolf Lammen, 20-Jan-2013.) $)
  consensus $p |- ( ( ( ( ph /\ ps ) \/ ( -. ph /\ ch ) ) \/ ( ps /\ ch ) ) <->
                      ( ( ph /\ ps ) \/ ( -. ph /\ ch ) ) ) $=
    ( wa wn wo id orc adantrr olc adantrl pm2.61ian jaoi impbii ) ABDZAEZCDZFZB
    CDZFRRRSRGASRABRCOQHIPCRBQOJKLMRSHN $.
    $( [20-Jan-2013] $) $( [16-May-2003] $)

  $( Theorem *4.42 of [WhiteheadRussell] p. 119.  (Contributed by Roy F.
     Longton, 21-Jun-2005.) $)
  pm4.42 $p |- ( ph <-> ( ( ph /\ ps ) \/ ( ph /\ -. ps ) ) ) $=
    ( wa wn wo wb dedlema dedlemb pm2.61i ) BAABCABDCEFBAAGBAAHI $.
    $( [21-Jun-2005] $)

  ${
    ninba.1 $e |- ph $.
    $( Miscellaneous inference relating falsehoods. $)
    ninba $p |- ( -. ps -> ( -. ph <-> ( ch /\ ps ) ) ) $=
      ( wn wa niabn bicomd ) BECBFAEABCDGH $.
      $( [31-Mar-1994] $)
  $}

  ${
    prlem1.1 $e |- ( ph -> ( et <-> ch ) ) $.
    prlem1.2 $e |- ( ps -> -. th ) $.
    $( A specialized lemma for set theory (to derive the Axiom of Pairing).
       (The proof was shortened by Andrew Salmon, 13-May-2011.)  (The proof was
       shortened by Wolf Lammen, 5-Jan-2013.) $)
    prlem1 $p |- ( ph -> ( ps ->
                  ( ( ( ps /\ ch ) \/ ( th /\ ta ) ) -> et ) ) ) $=
      ( wa wo wi biimprd adantld pm2.21d adantrd jaao ex ) ABBCIZDEIZJFKARFBSAC
      FBAFCGLMBDFEBDFHNOPQ $.
      $( [5-Jan-2013] $) $( [18-Oct-1995] $)
  $}

  $( A specialized lemma for set theory (to derive the Axiom of Pairing).  (The
     proof was shortened by Andrew Salmon, 13-May-2011.)  (The proof was
     shortened by Wolf Lammen, 9-Dec-2012.) $)
  prlem2 $p |- ( ( ( ph /\ ps ) \/ ( ch /\ th ) ) <->
              ( ( ph \/ ch ) /\ ( ( ph /\ ps ) \/ ( ch /\ th ) ) ) ) $=
    ( wa wo simpl orim12i pm4.71ri ) ABEZCDEZFACFJAKCABGCDGHI $.
    $( [9-Dec-2012] $) $( [5-Aug-1993] $)

  ${
    oplem1.1 $e |- ( ph -> ( ps \/ ch ) ) $.
    oplem1.2 $e |- ( ph -> ( th \/ ta ) ) $.
    oplem1.3 $e |- ( ps <-> th ) $.
    oplem1.4 $e |- ( ch -> ( th <-> ta ) ) $.
    $( A specialized lemma for set theory (ordered pair theorem).  (The proof
       was shortened by Wolf Lammen, 8-Dec-2012.) $)
    oplem1 $p |- ( ph -> ps ) $=
      ( wn wa notbii ord syl5bir jcad biimpar syl6 pm2.18d sylibr ) ADBADADJZCE
      KDATCETBJACBDHLABCFMNADEGMOCDEIPQRHS $.
      $( [8-Dec-2012] $) $( [18-Oct-1995] $)
  $}

  $( Lemma used in construction of real numbers.  (The proof was shortened by
     Andrew Salmon, 26-Jun-2011.) $)
  rnlem $p |- ( ( ( ph /\ ps ) /\ ( ch /\ th ) ) <->
  ( ( ( ph /\ ch ) /\ ( ps /\ th ) ) /\ ( ( ph /\ th ) /\ ( ps /\ ch ) ) ) ) $=
    ( wa an4 biimpi an42 biimpri jca adantl impbii ) ABECDEEZACEBDEEZADEBCEEZEM
    NOMNABCDFGOMADBCHZIJOMNOMPGKL $.
    $( [26-Jun-2011] $) $( [4-Sep-1995] $)

  $( A single axiom for Boolean algebra known as DN_1.  See
     ~ http://www-unix.mcs.anl.gov/~~mccune/papers/basax/v12.pdf .
     (Contributed by Jeffrey Hankins, 3-Jul-2009.)  (The proof was shortened by
     Andrew Salmon, 13-May-2011.)  (The proof was shortened by Wolf Lammen,
     6-Jan-2013.) $)
  dn1 $p |- ( -. ( -. ( -. ( ph \/ ps ) \/ ch ) \/
            -. ( ph \/ -. ( -. ch \/ -. ( ch \/ th ) ) ) ) <-> ch ) $=
    ( wo wn wa wi pm2.45 imnan mpbi biorfi orcom ordir 3bitri pm4.45 anor bitri
    orbi2i anbi2i 3bitrri ) CABEFZCEZACEZGZUCACFCDEZFEFZEZGUCFUHFEFCCUBAGZEUICE
    UEUICUBAFHUIFABIUBAJKLCUIMUBACNOUDUHUCCUGACCUFGUGCDPCUFQRSTUCUHQUA $.
    $( [6-Jan-2013] $) $( [22-Jun-2005] $)

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Abbreviated conjunction and disjunction of three wff's
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Extend wff definition to include 3-way disjunction ('or'). $)
  w3o $a wff ( ph \/ ps \/ ch ) $.
  $( Extend wff definition to include 3-way conjunction ('and'). $)
  w3a $a wff ( ph /\ ps /\ ch ) $.

  $( These abbreviations help eliminate parentheses to aid readability. $)

  $( Define disjunction ('or') of 3 wff's.  Definition *2.33 of
     [WhiteheadRussell] p. 105.  This abbreviation reduces the number of
     parentheses and emphasizes that the order of bracketing is not important
     by virtue of the associative law ~ orass . $)
  df-3or $a |- ( ( ph \/ ps \/ ch ) <-> ( ( ph \/ ps ) \/ ch ) ) $.

  $( Define conjunction ('and') of 3 wff.s.  Definition *4.34 of
     [WhiteheadRussell] p. 118.  This abbreviation reduces the number of
     parentheses and emphasizes that the order of bracketing is not important
     by virtue of the associative law ~ anass . $)
  df-3an $a |- ( ( ph /\ ps /\ ch ) <-> ( ( ph /\ ps ) /\ ch ) ) $.

  $( Associative law for triple disjunction. $)
  3orass $p |- ( ( ph \/ ps \/ ch ) <-> ( ph \/ ( ps \/ ch ) ) ) $=
    ( w3o wo df-3or orass bitri ) ABCDABECEABCEEABCFABCGH $.
    $( [8-Apr-1994] $)

  $( Associative law for triple conjunction. $)
  3anass $p |- ( ( ph /\ ps /\ ch ) <-> ( ph /\ ( ps /\ ch ) ) ) $=
    ( w3a wa df-3an anass bitri ) ABCDABECEABCEEABCFABCGH $.
    $( [8-Apr-1994] $)

  $( Rotation law for triple conjunction. $)
  3anrot $p |- ( ( ph /\ ps /\ ch ) <-> ( ps /\ ch /\ ph ) ) $=
    ( wa w3a ancom 3anass df-3an 3bitr4i ) ABCDZDJADABCEBCAEAJFABCGBCAHI $.
    $( [8-Apr-1994] $)

  $( Rotation law for triple disjunction. $)
  3orrot $p |- ( ( ph \/ ps \/ ch ) <-> ( ps \/ ch \/ ph ) ) $=
    ( wo w3o orcom 3orass df-3or 3bitr4i ) ABCDZDJADABCEBCAEAJFABCGBCAHI $.
    $( [4-Apr-1995] $)

  $( Commutation law for triple conjunction. $)
  3ancoma $p |- ( ( ph /\ ps /\ ch ) <-> ( ps /\ ph /\ ch ) ) $=
    ( wa w3a ancom anbi1i df-3an 3bitr4i ) ABDZCDBADZCDABCEBACEJKCABFGABCHBACHI
    $.
    $( [21-Apr-1994] $)

  $( Commutation law for triple conjunction. $)
  3ancomb $p |- ( ( ph /\ ps /\ ch ) <-> ( ph /\ ch /\ ps ) ) $=
    ( w3a 3ancoma 3anrot bitri ) ABCDBACDACBDABCEBACFG $.
    $( [21-Apr-1994] $)

  $( Commutation law for triple disjunction.  (Contributed by Scott Fenton,
     20-Apr-2011.) $)
  3orcomb $p |- ( ( ph \/ ps \/ ch ) <-> ( ph \/ ch \/ ps ) ) $=
    ( wo w3o orcom orbi2i 3orass 3bitr4i ) ABCDZDACBDZDABCEACBEJKABCFGABCHACBHI
    $.
    $( [20-Feb-2012] $) $( [20-Apr-2011] $)

  $( Reversal law for triple conjunction. $)
  3anrev $p |- ( ( ph /\ ps /\ ch ) <-> ( ch /\ ps /\ ph ) ) $=
    ( w3a 3ancoma 3anrot bitr4i ) ABCDBACDCBADABCECBAFG $.
    $( [21-Apr-1994] $)

  $( Triple conjunction expressed in terms of triple disjunction.  (Contributed
     by Jeff Hankins, 15-Aug-2009.) $)
  3anor $p |- ( ( ph /\ ps /\ ch ) <-> -. ( -. ph \/ -. ps \/ -. ch ) ) $=
    ( w3a wa wn w3o df-3an wo anor ianor orbi1i xchbinx df-3or xchbinxr bitri )
    ABCDABEZCEZAFZBFZCFZGZFABCHRSTIZUAIZUBRQFZUAIUDQCJUEUCUAABKLMSTUANOP $.
    $( [2-Mar-2011] $) $( [28-Jul-2009] $)

  $( Negated triple conjunction expressed in terms of triple disjunction.
     (Contributed by Jeff Hankins, 15-Aug-2009.)  (The proof was shortened by
     Andrew Salmon, 13-May-2011.) $)
  3ianor $p |- ( -. ( ph /\ ps /\ ch ) <-> ( -. ph \/ -. ps \/ -. ch ) ) $=
    ( wn w3o w3a 3anor con2bii bicomi ) ADBDCDEZABCFZDKJABCGHI $.
    $( [16-May-2011] $) $( [28-Jul-2009] $)

  $( Negated triple disjunction as triple conjunction.  (Contributed by Scott
     Fenton, 19-Apr-2011.) $)
  3ioran $p |- ( -. ( ph \/ ps \/ ch ) <-> ( -. ph /\ -. ps /\ -. ch ) ) $=
    ( wo wn wa w3o w3a ioran anbi1i df-3or xchnxbir df-3an 3bitr4i ) ABDZEZCEZF
    ZAEZBEZFZQFABCGZESTQHPUAQABIJOCDRUBOCIABCKLSTQMN $.
    $( [19-Apr-2011] $)

  $( Triple disjunction in terms of triple conjunction. $)
  3oran $p |- ( ( ph \/ ps \/ ch ) <-> -. ( -. ph /\ -. ps /\ -. ch ) ) $=
    ( wn w3a w3o 3ioran con1bii bicomi ) ADBDCDEZDABCFZKJABCGHI $.
    $( [8-Oct-2012] $)

  $( Simplification of triple conjunction. $)
  3simpa $p |- ( ( ph /\ ps /\ ch ) -> ( ph /\ ps ) ) $=
    ( w3a wa df-3an simplbi ) ABCDABECABCFG $.
    $( [21-Apr-1994] $)

  $( Simplification of triple conjunction. $)
  3simpb $p |- ( ( ph /\ ps /\ ch ) -> ( ph /\ ch ) ) $=
    ( w3a wa 3ancomb 3simpa sylbi ) ABCDACBDACEABCFACBGH $.
    $( [21-Apr-1994] $)

  $( Simplification of triple conjunction.  (The proof was shortened by Andrew
     Salmon, 13-May-2011.) $)
  3simpc $p |- ( ( ph /\ ps /\ ch ) -> ( ps /\ ch ) ) $=
    ( w3a wa 3anrot 3simpa sylbi ) ABCDBCADBCEABCFBCAGH $.
    $( [16-May-2011] $) $( [21-Apr-1994] $)

  $( Simplification of triple conjunction. $)
  simp1 $p |- ( ( ph /\ ps /\ ch ) -> ph ) $=
    ( w3a 3simpa simpld ) ABCDABABCEF $.
    $( [21-Apr-1994] $)

  $( Simplification of triple conjunction. $)
  simp2 $p |- ( ( ph /\ ps /\ ch ) -> ps ) $=
    ( w3a 3simpa simprd ) ABCDABABCEF $.
    $( [21-Apr-1994] $)

  $( Simplification of triple conjunction. $)
  simp3 $p |- ( ( ph /\ ps /\ ch ) -> ch ) $=
    ( w3a 3simpc simprd ) ABCDBCABCEF $.
    $( [21-Apr-1994] $)

  $( Simplification rule.  (Contributed by Jeff Hankins, 17-Nov-2009.) $)
  simpl1 $p |- ( ( ( ph /\ ps /\ ch ) /\ th ) -> ph ) $=
    ( w3a simp1 adantr ) ABCEADABCFG $.
    $( [17-Nov-2009] $)

  $( Simplification rule.  (Contributed by Jeff Hankins, 17-Nov-2009.) $)
  simpl2 $p |- ( ( ( ph /\ ps /\ ch ) /\ th ) -> ps ) $=
    ( w3a simp2 adantr ) ABCEBDABCFG $.
    $( [17-Nov-2009] $)

  $( Simplification rule.  (Contributed by Jeff Hankins, 17-Nov-2009.) $)
  simpl3 $p |- ( ( ( ph /\ ps /\ ch ) /\ th ) -> ch ) $=
    ( w3a simp3 adantr ) ABCECDABCFG $.
    $( [17-Nov-2009] $)

  $( Simplification rule.  (Contributed by Jeff Hankins, 17-Nov-2009.) $)
  simpr1 $p |- ( ( ph /\ ( ps /\ ch /\ th ) ) -> ps ) $=
    ( w3a simp1 adantl ) BCDEBABCDFG $.
    $( [17-Nov-2009] $)

  $( Simplification rule.  (Contributed by Jeff Hankins, 17-Nov-2009.) $)
  simpr2 $p |- ( ( ph /\ ( ps /\ ch /\ th ) ) -> ch ) $=
    ( w3a simp2 adantl ) BCDECABCDFG $.
    $( [17-Nov-2009] $)

  $( Simplification rule.  (Contributed by Jeff Hankins, 17-Nov-2009.) $)
  simpr3 $p |- ( ( ph /\ ( ps /\ ch /\ th ) ) -> th ) $=
    ( w3a simp3 adantl ) BCDEDABCDFG $.
    $( [17-Nov-2009] $)

  ${
    3simp1i.1 $e |- ( ph /\ ps /\ ch ) $.
    $( Infer a conjunct from a triple conjunction. $)
    simp1i $p |- ph $=
      ( w3a simp1 ax-mp ) ABCEADABCFG $.
      $( [19-Apr-2005] $)

    $( Infer a conjunct from a triple conjunction. $)
    simp2i $p |- ps $=
      ( w3a simp2 ax-mp ) ABCEBDABCFG $.
      $( [19-Apr-2005] $)

    $( Infer a conjunct from a triple conjunction. $)
    simp3i $p |- ch $=
      ( w3a simp3 ax-mp ) ABCECDABCFG $.
      $( [19-Apr-2005] $)
  $}

  ${
    3simp1d.1 $e |- ( ph -> ( ps /\ ch /\ th ) ) $.
    $( Deduce a conjunct from a triple conjunction. $)
    simp1d $p |- ( ph -> ps ) $=
      ( w3a simp1 syl ) ABCDFBEBCDGH $.
      $( [4-Sep-2005] $)

    $( Deduce a conjunct from a triple conjunction. $)
    simp2d $p |- ( ph -> ch ) $=
      ( w3a simp2 syl ) ABCDFCEBCDGH $.
      $( [4-Sep-2005] $)

    $( Deduce a conjunct from a triple conjunction. $)
    simp3d $p |- ( ph -> th ) $=
      ( w3a simp3 syl ) ABCDFDEBCDGH $.
      $( [4-Sep-2005] $)
  $}

  ${
    3simp1bi.1 $e |- ( ph <-> ( ps /\ ch /\ th ) ) $.
    $( Deduce a conjunct from a triple conjunction.  (Contributed by Jonathan
       Ben-Naim, 3-Jun-2011.) $)
    simp1bi $p |- ( ph -> ps ) $=
      ( w3a biimpi simp1d ) ABCDABCDFEGH $.
      $( [9-Sep-2011] $) $( [3-Jun-2011] $)

    $( Deduce a conjunct from a triple conjunction.  (Contributed by Jonathan
       Ben-Naim, 3-Jun-2011.) $)
    simp2bi $p |- ( ph -> ch ) $=
      ( w3a biimpi simp2d ) ABCDABCDFEGH $.
      $( [9-Sep-2011] $) $( [3-Jun-2011] $)

    $( Deduce a conjunct from a triple conjunction.  (Contributed by Jonathan
       Ben-Naim, 3-Jun-2011.) $)
    simp3bi $p |- ( ph -> th ) $=
      ( w3a biimpi simp3d ) ABCDABCDFEGH $.
      $( [9-Sep-2011] $) $( [3-Jun-2011] $)
  $}

  ${
    3adant.1 $e |- ( ( ph /\ ps ) -> ch ) $.
    $( Deduction adding a conjunct to antecedent. $)
    3adant1 $p |- ( ( th /\ ph /\ ps ) -> ch ) $=
      ( w3a wa 3simpc syl ) DABFABGCDABHEI $.
      $( [16-Jul-1995] $)

    $( Deduction adding a conjunct to antecedent. $)
    3adant2 $p |- ( ( ph /\ th /\ ps ) -> ch ) $=
      ( w3a wa 3simpb syl ) ADBFABGCADBHEI $.
      $( [16-Jul-1995] $)

    $( Deduction adding a conjunct to antecedent. $)
    3adant3 $p |- ( ( ph /\ ps /\ th ) -> ch ) $=
      ( w3a wa 3simpa syl ) ABDFABGCABDHEI $.
      $( [16-Jul-1995] $)
  $}

  ${
    3ad2ant.1 $e |- ( ph -> ch ) $.
    $( Deduction adding conjuncts to an antecedent. $)
    3ad2ant1 $p |- ( ( ph /\ ps /\ th ) -> ch ) $=
      ( adantr 3adant2 ) ADCBACDEFG $.
      $( [21-Apr-2005] $)

    $( Deduction adding conjuncts to an antecedent. $)
    3ad2ant2 $p |- ( ( ps /\ ph /\ th ) -> ch ) $=
      ( adantr 3adant1 ) ADCBACDEFG $.
      $( [21-Apr-2005] $)

    $( Deduction adding conjuncts to an antecedent. $)
    3ad2ant3 $p |- ( ( ps /\ th /\ ph ) -> ch ) $=
      ( adantl 3adant1 ) DACBACDEFG $.
      $( [21-Apr-2005] $)
  $}

  $( Simplification of triple conjunction. $)
  simp1l $p |- ( ( ( ph /\ ps ) /\ ch /\ th ) -> ph ) $=
    ( wa simpl 3ad2ant1 ) ABECADABFG $.
    $( [9-Nov-2011] $)

  $( Simplification of triple conjunction. $)
  simp1r $p |- ( ( ( ph /\ ps ) /\ ch /\ th ) -> ps ) $=
    ( wa simpr 3ad2ant1 ) ABECBDABFG $.
    $( [9-Nov-2011] $)

  $( Simplification of triple conjunction. $)
  simp2l $p |- ( ( ph /\ ( ps /\ ch ) /\ th ) -> ps ) $=
    ( wa simpl 3ad2ant2 ) BCEABDBCFG $.
    $( [9-Nov-2011] $)

  $( Simplification of triple conjunction. $)
  simp2r $p |- ( ( ph /\ ( ps /\ ch ) /\ th ) -> ch ) $=
    ( wa simpr 3ad2ant2 ) BCEACDBCFG $.
    $( [9-Nov-2011] $)

  $( Simplification of triple conjunction. $)
  simp3l $p |- ( ( ph /\ ps /\ ( ch /\ th ) ) -> ch ) $=
    ( wa simpl 3ad2ant3 ) CDEACBCDFG $.
    $( [9-Nov-2011] $)

  $( Simplification of triple conjunction. $)
  simp3r $p |- ( ( ph /\ ps /\ ( ch /\ th ) ) -> th ) $=
    ( wa simpr 3ad2ant3 ) CDEADBCDFG $.
    $( [9-Nov-2011] $)

  $( Simplification of doubly triple conjunction. $)
  simp11 $p |- ( ( ( ph /\ ps /\ ch ) /\ th /\ ta ) -> ph ) $=
    ( w3a simp1 3ad2ant1 ) ABCFDAEABCGH $.
    $( [17-Nov-2011] $)

  $( Simplification of doubly triple conjunction. $)
  simp12 $p |- ( ( ( ph /\ ps /\ ch ) /\ th /\ ta ) -> ps ) $=
    ( w3a simp2 3ad2ant1 ) ABCFDBEABCGH $.
    $( [17-Nov-2011] $)

  $( Simplification of doubly triple conjunction. $)
  simp13 $p |- ( ( ( ph /\ ps /\ ch ) /\ th /\ ta ) -> ch ) $=
    ( w3a simp3 3ad2ant1 ) ABCFDCEABCGH $.
    $( [17-Nov-2011] $)

  $( Simplification of doubly triple conjunction. $)
  simp21 $p |- ( ( ph /\ ( ps /\ ch /\ th ) /\ ta ) -> ps ) $=
    ( w3a simp1 3ad2ant2 ) BCDFABEBCDGH $.
    $( [17-Nov-2011] $)

  $( Simplification of doubly triple conjunction. $)
  simp22 $p |- ( ( ph /\ ( ps /\ ch /\ th ) /\ ta ) -> ch ) $=
    ( w3a simp2 3ad2ant2 ) BCDFACEBCDGH $.
    $( [17-Nov-2011] $)

  $( Simplification of doubly triple conjunction. $)
  simp23 $p |- ( ( ph /\ ( ps /\ ch /\ th ) /\ ta ) -> th ) $=
    ( w3a simp3 3ad2ant2 ) BCDFADEBCDGH $.
    $( [17-Nov-2011] $)

  $( Simplification of doubly triple conjunction. $)
  simp31 $p |- ( ( ph /\ ps /\ ( ch /\ th /\ ta ) ) -> ch ) $=
    ( w3a simp1 3ad2ant3 ) CDEFACBCDEGH $.
    $( [17-Nov-2011] $)

  $( Simplification of doubly triple conjunction. $)
  simp32 $p |- ( ( ph /\ ps /\ ( ch /\ th /\ ta ) ) -> th ) $=
    ( w3a simp2 3ad2ant3 ) CDEFADBCDEGH $.
    $( [17-Nov-2011] $)

  $( Simplification of doubly triple conjunction. $)
  simp33 $p |- ( ( ph /\ ps /\ ( ch /\ th /\ ta ) ) -> ta ) $=
    ( w3a simp3 3ad2ant3 ) CDEFAEBCDEGH $.
    $( [17-Nov-2011] $)

  $( Simplification of conjunction. $)
  simpll1 $p |- ( ( ( ( ph /\ ps /\ ch ) /\ th ) /\ ta ) -> ph ) $=
    ( w3a wa simpl1 adantr ) ABCFDGAEABCDHI $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simpll2 $p |- ( ( ( ( ph /\ ps /\ ch ) /\ th ) /\ ta ) -> ps ) $=
    ( w3a wa simpl2 adantr ) ABCFDGBEABCDHI $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simpll3 $p |- ( ( ( ( ph /\ ps /\ ch ) /\ th ) /\ ta ) -> ch ) $=
    ( w3a wa simpl3 adantr ) ABCFDGCEABCDHI $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simplr1 $p |- ( ( ( th /\ ( ph /\ ps /\ ch ) ) /\ ta ) -> ph ) $=
    ( w3a wa simpr1 adantr ) DABCFGAEDABCHI $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simplr2 $p |- ( ( ( th /\ ( ph /\ ps /\ ch ) ) /\ ta ) -> ps ) $=
    ( w3a wa simpr2 adantr ) DABCFGBEDABCHI $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simplr3 $p |- ( ( ( th /\ ( ph /\ ps /\ ch ) ) /\ ta ) -> ch ) $=
    ( w3a wa simpr3 adantr ) DABCFGCEDABCHI $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simprl1 $p |- ( ( ta /\ ( ( ph /\ ps /\ ch ) /\ th ) ) -> ph ) $=
    ( w3a wa simpl1 adantl ) ABCFDGAEABCDHI $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simprl2 $p |- ( ( ta /\ ( ( ph /\ ps /\ ch ) /\ th ) ) -> ps ) $=
    ( w3a wa simpl2 adantl ) ABCFDGBEABCDHI $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simprl3 $p |- ( ( ta /\ ( ( ph /\ ps /\ ch ) /\ th ) ) -> ch ) $=
    ( w3a wa simpl3 adantl ) ABCFDGCEABCDHI $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simprr1 $p |- ( ( ta /\ ( th /\ ( ph /\ ps /\ ch ) ) ) -> ph ) $=
    ( w3a wa simpr1 adantl ) DABCFGAEDABCHI $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simprr2 $p |- ( ( ta /\ ( th /\ ( ph /\ ps /\ ch ) ) ) -> ps ) $=
    ( w3a wa simpr2 adantl ) DABCFGBEDABCHI $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simprr3 $p |- ( ( ta /\ ( th /\ ( ph /\ ps /\ ch ) ) ) -> ch ) $=
    ( w3a wa simpr3 adantl ) DABCFGCEDABCHI $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simpl1l $p |- ( ( ( ( ph /\ ps ) /\ ch /\ th ) /\ ta ) -> ph ) $=
    ( wa w3a simp1l adantr ) ABFCDGAEABCDHI $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simpl1r $p |- ( ( ( ( ph /\ ps ) /\ ch /\ th ) /\ ta ) -> ps ) $=
    ( wa w3a simp1r adantr ) ABFCDGBEABCDHI $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simpl2l $p |- ( ( ( ch /\ ( ph /\ ps ) /\ th ) /\ ta ) -> ph ) $=
    ( wa w3a simp2l adantr ) CABFDGAECABDHI $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simpl2r $p |- ( ( ( ch /\ ( ph /\ ps ) /\ th ) /\ ta ) -> ps ) $=
    ( wa w3a simp2r adantr ) CABFDGBECABDHI $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simpl3l $p |- ( ( ( ch /\ th /\ ( ph /\ ps ) ) /\ ta ) -> ph ) $=
    ( wa w3a simp3l adantr ) CDABFGAECDABHI $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simpl3r $p |- ( ( ( ch /\ th /\ ( ph /\ ps ) ) /\ ta ) -> ps ) $=
    ( wa w3a simp3r adantr ) CDABFGBECDABHI $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simpr1l $p |- ( ( ta /\ ( ( ph /\ ps ) /\ ch /\ th ) ) -> ph ) $=
    ( wa w3a simp1l adantl ) ABFCDGAEABCDHI $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simpr1r $p |- ( ( ta /\ ( ( ph /\ ps ) /\ ch /\ th ) ) -> ps ) $=
    ( wa w3a simp1r adantl ) ABFCDGBEABCDHI $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simpr2l $p |- ( ( ta /\ ( ch /\ ( ph /\ ps ) /\ th ) ) -> ph ) $=
    ( wa w3a simp2l adantl ) CABFDGAECABDHI $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simpr2r $p |- ( ( ta /\ ( ch /\ ( ph /\ ps ) /\ th ) ) -> ps ) $=
    ( wa w3a simp2r adantl ) CABFDGBECABDHI $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simpr3l $p |- ( ( ta /\ ( ch /\ th /\ ( ph /\ ps ) ) ) -> ph ) $=
    ( wa w3a simp3l adantl ) CDABFGAECDABHI $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simpr3r $p |- ( ( ta /\ ( ch /\ th /\ ( ph /\ ps ) ) ) -> ps ) $=
    ( wa w3a simp3r adantl ) CDABFGBECDABHI $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simp1ll $p |- ( ( ( ( ph /\ ps ) /\ ch ) /\ th /\ ta ) -> ph ) $=
    ( wa simpll 3ad2ant1 ) ABFCFDAEABCGH $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simp1lr $p |- ( ( ( ( ph /\ ps ) /\ ch ) /\ th /\ ta ) -> ps ) $=
    ( wa simplr 3ad2ant1 ) ABFCFDBEABCGH $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simp1rl $p |- ( ( ( ch /\ ( ph /\ ps ) ) /\ th /\ ta ) -> ph ) $=
    ( wa simprl 3ad2ant1 ) CABFFDAECABGH $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simp1rr $p |- ( ( ( ch /\ ( ph /\ ps ) ) /\ th /\ ta ) -> ps ) $=
    ( wa simprr 3ad2ant1 ) CABFFDBECABGH $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simp2ll $p |- ( ( th /\ ( ( ph /\ ps ) /\ ch ) /\ ta ) -> ph ) $=
    ( wa simpll 3ad2ant2 ) ABFCFDAEABCGH $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simp2lr $p |- ( ( th /\ ( ( ph /\ ps ) /\ ch ) /\ ta ) -> ps ) $=
    ( wa simplr 3ad2ant2 ) ABFCFDBEABCGH $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simp2rl $p |- ( ( th /\ ( ch /\ ( ph /\ ps ) ) /\ ta ) -> ph ) $=
    ( wa simprl 3ad2ant2 ) CABFFDAECABGH $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simp2rr $p |- ( ( th /\ ( ch /\ ( ph /\ ps ) ) /\ ta ) -> ps ) $=
    ( wa simprr 3ad2ant2 ) CABFFDBECABGH $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simp3ll $p |- ( ( th /\ ta /\ ( ( ph /\ ps ) /\ ch ) ) -> ph ) $=
    ( wa simpll 3ad2ant3 ) ABFCFDAEABCGH $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simp3lr $p |- ( ( th /\ ta /\ ( ( ph /\ ps ) /\ ch ) ) -> ps ) $=
    ( wa simplr 3ad2ant3 ) ABFCFDBEABCGH $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simp3rl $p |- ( ( th /\ ta /\ ( ch /\ ( ph /\ ps ) ) ) -> ph ) $=
    ( wa simprl 3ad2ant3 ) CABFFDAECABGH $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simp3rr $p |- ( ( th /\ ta /\ ( ch /\ ( ph /\ ps ) ) ) -> ps ) $=
    ( wa simprr 3ad2ant3 ) CABFFDBECABGH $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simpl11 $p |- ( ( ( ( ph /\ ps /\ ch ) /\ th /\ ta ) /\ et ) -> ph ) $=
    ( w3a simp11 adantr ) ABCGDEGAFABCDEHI $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simpl12 $p |- ( ( ( ( ph /\ ps /\ ch ) /\ th /\ ta ) /\ et ) -> ps ) $=
    ( w3a simp12 adantr ) ABCGDEGBFABCDEHI $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simpl13 $p |- ( ( ( ( ph /\ ps /\ ch ) /\ th /\ ta ) /\ et ) -> ch ) $=
    ( w3a simp13 adantr ) ABCGDEGCFABCDEHI $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simpl21 $p |- ( ( ( th /\ ( ph /\ ps /\ ch ) /\ ta ) /\ et ) -> ph ) $=
    ( w3a simp21 adantr ) DABCGEGAFDABCEHI $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simpl22 $p |- ( ( ( th /\ ( ph /\ ps /\ ch ) /\ ta ) /\ et ) -> ps ) $=
    ( w3a simp22 adantr ) DABCGEGBFDABCEHI $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simpl23 $p |- ( ( ( th /\ ( ph /\ ps /\ ch ) /\ ta ) /\ et ) -> ch ) $=
    ( w3a simp23 adantr ) DABCGEGCFDABCEHI $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simpl31 $p |- ( ( ( th /\ ta /\ ( ph /\ ps /\ ch ) ) /\ et ) -> ph ) $=
    ( w3a simp31 adantr ) DEABCGGAFDEABCHI $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simpl32 $p |- ( ( ( th /\ ta /\ ( ph /\ ps /\ ch ) ) /\ et ) -> ps ) $=
    ( w3a simp32 adantr ) DEABCGGBFDEABCHI $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simpl33 $p |- ( ( ( th /\ ta /\ ( ph /\ ps /\ ch ) ) /\ et ) -> ch ) $=
    ( w3a simp33 adantr ) DEABCGGCFDEABCHI $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simpr11 $p |- ( ( et /\ ( ( ph /\ ps /\ ch ) /\ th /\ ta ) ) -> ph ) $=
    ( w3a simp11 adantl ) ABCGDEGAFABCDEHI $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simpr12 $p |- ( ( et /\ ( ( ph /\ ps /\ ch ) /\ th /\ ta ) ) -> ps ) $=
    ( w3a simp12 adantl ) ABCGDEGBFABCDEHI $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simpr13 $p |- ( ( et /\ ( ( ph /\ ps /\ ch ) /\ th /\ ta ) ) -> ch ) $=
    ( w3a simp13 adantl ) ABCGDEGCFABCDEHI $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simpr21 $p |- ( ( et /\ ( th /\ ( ph /\ ps /\ ch ) /\ ta ) ) -> ph ) $=
    ( w3a simp21 adantl ) DABCGEGAFDABCEHI $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simpr22 $p |- ( ( et /\ ( th /\ ( ph /\ ps /\ ch ) /\ ta ) ) -> ps ) $=
    ( w3a simp22 adantl ) DABCGEGBFDABCEHI $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simpr23 $p |- ( ( et /\ ( th /\ ( ph /\ ps /\ ch ) /\ ta ) ) -> ch ) $=
    ( w3a simp23 adantl ) DABCGEGCFDABCEHI $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simpr31 $p |- ( ( et /\ ( th /\ ta /\ ( ph /\ ps /\ ch ) ) ) -> ph ) $=
    ( w3a simp31 adantl ) DEABCGGAFDEABCHI $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simpr32 $p |- ( ( et /\ ( th /\ ta /\ ( ph /\ ps /\ ch ) ) ) -> ps ) $=
    ( w3a simp32 adantl ) DEABCGGBFDEABCHI $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simpr33 $p |- ( ( et /\ ( th /\ ta /\ ( ph /\ ps /\ ch ) ) ) -> ch ) $=
    ( w3a simp33 adantl ) DEABCGGCFDEABCHI $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simp1l1 $p |- ( ( ( ( ph /\ ps /\ ch ) /\ th ) /\ ta /\ et ) -> ph ) $=
    ( w3a wa simpl1 3ad2ant1 ) ABCGDHEAFABCDIJ $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simp1l2 $p |- ( ( ( ( ph /\ ps /\ ch ) /\ th ) /\ ta /\ et ) -> ps ) $=
    ( w3a wa simpl2 3ad2ant1 ) ABCGDHEBFABCDIJ $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simp1l3 $p |- ( ( ( ( ph /\ ps /\ ch ) /\ th ) /\ ta /\ et ) -> ch ) $=
    ( w3a wa simpl3 3ad2ant1 ) ABCGDHECFABCDIJ $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simp1r1 $p |- ( ( ( th /\ ( ph /\ ps /\ ch ) ) /\ ta /\ et ) -> ph ) $=
    ( w3a wa simpr1 3ad2ant1 ) DABCGHEAFDABCIJ $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simp1r2 $p |- ( ( ( th /\ ( ph /\ ps /\ ch ) ) /\ ta /\ et ) -> ps ) $=
    ( w3a wa simpr2 3ad2ant1 ) DABCGHEBFDABCIJ $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simp1r3 $p |- ( ( ( th /\ ( ph /\ ps /\ ch ) ) /\ ta /\ et ) -> ch ) $=
    ( w3a wa simpr3 3ad2ant1 ) DABCGHECFDABCIJ $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simp2l1 $p |- ( ( ta /\ ( ( ph /\ ps /\ ch ) /\ th ) /\ et ) -> ph ) $=
    ( w3a wa simpl1 3ad2ant2 ) ABCGDHEAFABCDIJ $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simp2l2 $p |- ( ( ta /\ ( ( ph /\ ps /\ ch ) /\ th ) /\ et ) -> ps ) $=
    ( w3a wa simpl2 3ad2ant2 ) ABCGDHEBFABCDIJ $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simp2l3 $p |- ( ( ta /\ ( ( ph /\ ps /\ ch ) /\ th ) /\ et ) -> ch ) $=
    ( w3a wa simpl3 3ad2ant2 ) ABCGDHECFABCDIJ $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simp2r1 $p |- ( ( ta /\ ( th /\ ( ph /\ ps /\ ch ) ) /\ et ) -> ph ) $=
    ( w3a wa simpr1 3ad2ant2 ) DABCGHEAFDABCIJ $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simp2r2 $p |- ( ( ta /\ ( th /\ ( ph /\ ps /\ ch ) ) /\ et ) -> ps ) $=
    ( w3a wa simpr2 3ad2ant2 ) DABCGHEBFDABCIJ $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simp2r3 $p |- ( ( ta /\ ( th /\ ( ph /\ ps /\ ch ) ) /\ et ) -> ch ) $=
    ( w3a wa simpr3 3ad2ant2 ) DABCGHECFDABCIJ $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simp3l1 $p |- ( ( ta /\ et /\ ( ( ph /\ ps /\ ch ) /\ th ) ) -> ph ) $=
    ( w3a wa simpl1 3ad2ant3 ) ABCGDHEAFABCDIJ $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simp3l2 $p |- ( ( ta /\ et /\ ( ( ph /\ ps /\ ch ) /\ th ) ) -> ps ) $=
    ( w3a wa simpl2 3ad2ant3 ) ABCGDHEBFABCDIJ $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simp3l3 $p |- ( ( ta /\ et /\ ( ( ph /\ ps /\ ch ) /\ th ) ) -> ch ) $=
    ( w3a wa simpl3 3ad2ant3 ) ABCGDHECFABCDIJ $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simp3r1 $p |- ( ( ta /\ et /\ ( th /\ ( ph /\ ps /\ ch ) ) ) -> ph ) $=
    ( w3a wa simpr1 3ad2ant3 ) DABCGHEAFDABCIJ $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simp3r2 $p |- ( ( ta /\ et /\ ( th /\ ( ph /\ ps /\ ch ) ) ) -> ps ) $=
    ( w3a wa simpr2 3ad2ant3 ) DABCGHEBFDABCIJ $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simp3r3 $p |- ( ( ta /\ et /\ ( th /\ ( ph /\ ps /\ ch ) ) ) -> ch ) $=
    ( w3a wa simpr3 3ad2ant3 ) DABCGHECFDABCIJ $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simp11l $p |- ( ( ( ( ph /\ ps ) /\ ch /\ th ) /\ ta /\ et ) -> ph ) $=
    ( wa w3a simp1l 3ad2ant1 ) ABGCDHEAFABCDIJ $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simp11r $p |- ( ( ( ( ph /\ ps ) /\ ch /\ th ) /\ ta /\ et ) -> ps ) $=
    ( wa w3a simp1r 3ad2ant1 ) ABGCDHEBFABCDIJ $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simp12l $p |- ( ( ( ch /\ ( ph /\ ps ) /\ th ) /\ ta /\ et ) -> ph ) $=
    ( wa w3a simp2l 3ad2ant1 ) CABGDHEAFCABDIJ $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simp12r $p |- ( ( ( ch /\ ( ph /\ ps ) /\ th ) /\ ta /\ et ) -> ps ) $=
    ( wa w3a simp2r 3ad2ant1 ) CABGDHEBFCABDIJ $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simp13l $p |- ( ( ( ch /\ th /\ ( ph /\ ps ) ) /\ ta /\ et ) -> ph ) $=
    ( wa w3a simp3l 3ad2ant1 ) CDABGHEAFCDABIJ $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simp13r $p |- ( ( ( ch /\ th /\ ( ph /\ ps ) ) /\ ta /\ et ) -> ps ) $=
    ( wa w3a simp3r 3ad2ant1 ) CDABGHEBFCDABIJ $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simp21l $p |- ( ( ta /\ ( ( ph /\ ps ) /\ ch /\ th ) /\ et ) -> ph ) $=
    ( wa w3a simp1l 3ad2ant2 ) ABGCDHEAFABCDIJ $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simp21r $p |- ( ( ta /\ ( ( ph /\ ps ) /\ ch /\ th ) /\ et ) -> ps ) $=
    ( wa w3a simp1r 3ad2ant2 ) ABGCDHEBFABCDIJ $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simp22l $p |- ( ( ta /\ ( ch /\ ( ph /\ ps ) /\ th ) /\ et ) -> ph ) $=
    ( wa w3a simp2l 3ad2ant2 ) CABGDHEAFCABDIJ $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simp22r $p |- ( ( ta /\ ( ch /\ ( ph /\ ps ) /\ th ) /\ et ) -> ps ) $=
    ( wa w3a simp2r 3ad2ant2 ) CABGDHEBFCABDIJ $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simp23l $p |- ( ( ta /\ ( ch /\ th /\ ( ph /\ ps ) ) /\ et ) -> ph ) $=
    ( wa w3a simp3l 3ad2ant2 ) CDABGHEAFCDABIJ $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simp23r $p |- ( ( ta /\ ( ch /\ th /\ ( ph /\ ps ) ) /\ et ) -> ps ) $=
    ( wa w3a simp3r 3ad2ant2 ) CDABGHEBFCDABIJ $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simp31l $p |- ( ( ta /\ et /\ ( ( ph /\ ps ) /\ ch /\ th ) ) -> ph ) $=
    ( wa w3a simp1l 3ad2ant3 ) ABGCDHEAFABCDIJ $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simp31r $p |- ( ( ta /\ et /\ ( ( ph /\ ps ) /\ ch /\ th ) ) -> ps ) $=
    ( wa w3a simp1r 3ad2ant3 ) ABGCDHEBFABCDIJ $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simp32l $p |- ( ( ta /\ et /\ ( ch /\ ( ph /\ ps ) /\ th ) ) -> ph ) $=
    ( wa w3a simp2l 3ad2ant3 ) CABGDHEAFCABDIJ $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simp32r $p |- ( ( ta /\ et /\ ( ch /\ ( ph /\ ps ) /\ th ) ) -> ps ) $=
    ( wa w3a simp2r 3ad2ant3 ) CABGDHEBFCABDIJ $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simp33l $p |- ( ( ta /\ et /\ ( ch /\ th /\ ( ph /\ ps ) ) ) -> ph ) $=
    ( wa w3a simp3l 3ad2ant3 ) CDABGHEAFCDABIJ $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simp33r $p |- ( ( ta /\ et /\ ( ch /\ th /\ ( ph /\ ps ) ) ) -> ps ) $=
    ( wa w3a simp3r 3ad2ant3 ) CDABGHEBFCDABIJ $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simp111 $p |- ( ( ( ( ph /\ ps /\ ch ) /\ th /\ ta ) /\ et /\ ze ) -> ph ) $=
    ( w3a simp11 3ad2ant1 ) ABCHDEHFAGABCDEIJ $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simp112 $p |- ( ( ( ( ph /\ ps /\ ch ) /\ th /\ ta ) /\ et /\ ze ) -> ps ) $=
    ( w3a simp12 3ad2ant1 ) ABCHDEHFBGABCDEIJ $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simp113 $p |- ( ( ( ( ph /\ ps /\ ch ) /\ th /\ ta ) /\ et /\ ze ) -> ch ) $=
    ( w3a simp13 3ad2ant1 ) ABCHDEHFCGABCDEIJ $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simp121 $p |- ( ( ( th /\ ( ph /\ ps /\ ch ) /\ ta ) /\ et /\ ze ) -> ph ) $=
    ( w3a simp21 3ad2ant1 ) DABCHEHFAGDABCEIJ $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simp122 $p |- ( ( ( th /\ ( ph /\ ps /\ ch ) /\ ta ) /\ et /\ ze ) -> ps ) $=
    ( w3a simp22 3ad2ant1 ) DABCHEHFBGDABCEIJ $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simp123 $p |- ( ( ( th /\ ( ph /\ ps /\ ch ) /\ ta ) /\ et /\ ze ) -> ch ) $=
    ( w3a simp23 3ad2ant1 ) DABCHEHFCGDABCEIJ $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simp131 $p |- ( ( ( th /\ ta /\ ( ph /\ ps /\ ch ) ) /\ et /\ ze ) -> ph ) $=
    ( w3a simp31 3ad2ant1 ) DEABCHHFAGDEABCIJ $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simp132 $p |- ( ( ( th /\ ta /\ ( ph /\ ps /\ ch ) ) /\ et /\ ze ) -> ps ) $=
    ( w3a simp32 3ad2ant1 ) DEABCHHFBGDEABCIJ $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simp133 $p |- ( ( ( th /\ ta /\ ( ph /\ ps /\ ch ) ) /\ et /\ ze ) -> ch ) $=
    ( w3a simp33 3ad2ant1 ) DEABCHHFCGDEABCIJ $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simp211 $p |- ( ( et /\ ( ( ph /\ ps /\ ch ) /\ th /\ ta ) /\ ze ) -> ph ) $=
    ( w3a simp11 3ad2ant2 ) ABCHDEHFAGABCDEIJ $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simp212 $p |- ( ( et /\ ( ( ph /\ ps /\ ch ) /\ th /\ ta ) /\ ze ) -> ps ) $=
    ( w3a simp12 3ad2ant2 ) ABCHDEHFBGABCDEIJ $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simp213 $p |- ( ( et /\ ( ( ph /\ ps /\ ch ) /\ th /\ ta ) /\ ze ) -> ch ) $=
    ( w3a simp13 3ad2ant2 ) ABCHDEHFCGABCDEIJ $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simp221 $p |- ( ( et /\ ( th /\ ( ph /\ ps /\ ch ) /\ ta ) /\ ze ) -> ph ) $=
    ( w3a simp21 3ad2ant2 ) DABCHEHFAGDABCEIJ $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simp222 $p |- ( ( et /\ ( th /\ ( ph /\ ps /\ ch ) /\ ta ) /\ ze ) -> ps ) $=
    ( w3a simp22 3ad2ant2 ) DABCHEHFBGDABCEIJ $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simp223 $p |- ( ( et /\ ( th /\ ( ph /\ ps /\ ch ) /\ ta ) /\ ze ) -> ch ) $=
    ( w3a simp23 3ad2ant2 ) DABCHEHFCGDABCEIJ $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simp231 $p |- ( ( et /\ ( th /\ ta /\ ( ph /\ ps /\ ch ) ) /\ ze ) -> ph ) $=
    ( w3a simp31 3ad2ant2 ) DEABCHHFAGDEABCIJ $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simp232 $p |- ( ( et /\ ( th /\ ta /\ ( ph /\ ps /\ ch ) ) /\ ze ) -> ps ) $=
    ( w3a simp32 3ad2ant2 ) DEABCHHFBGDEABCIJ $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simp233 $p |- ( ( et /\ ( th /\ ta /\ ( ph /\ ps /\ ch ) ) /\ ze ) -> ch ) $=
    ( w3a simp33 3ad2ant2 ) DEABCHHFCGDEABCIJ $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simp311 $p |- ( ( et /\ ze /\ ( ( ph /\ ps /\ ch ) /\ th /\ ta ) ) -> ph ) $=
    ( w3a simp11 3ad2ant3 ) ABCHDEHFAGABCDEIJ $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simp312 $p |- ( ( et /\ ze /\ ( ( ph /\ ps /\ ch ) /\ th /\ ta ) ) -> ps ) $=
    ( w3a simp12 3ad2ant3 ) ABCHDEHFBGABCDEIJ $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simp313 $p |- ( ( et /\ ze /\ ( ( ph /\ ps /\ ch ) /\ th /\ ta ) ) -> ch ) $=
    ( w3a simp13 3ad2ant3 ) ABCHDEHFCGABCDEIJ $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simp321 $p |- ( ( et /\ ze /\ ( th /\ ( ph /\ ps /\ ch ) /\ ta ) ) -> ph ) $=
    ( w3a simp21 3ad2ant3 ) DABCHEHFAGDABCEIJ $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simp322 $p |- ( ( et /\ ze /\ ( th /\ ( ph /\ ps /\ ch ) /\ ta ) ) -> ps ) $=
    ( w3a simp22 3ad2ant3 ) DABCHEHFBGDABCEIJ $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simp323 $p |- ( ( et /\ ze /\ ( th /\ ( ph /\ ps /\ ch ) /\ ta ) ) -> ch ) $=
    ( w3a simp23 3ad2ant3 ) DABCHEHFCGDABCEIJ $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simp331 $p |- ( ( et /\ ze /\ ( th /\ ta /\ ( ph /\ ps /\ ch ) ) ) -> ph ) $=
    ( w3a simp31 3ad2ant3 ) DEABCHHFAGDEABCIJ $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simp332 $p |- ( ( et /\ ze /\ ( th /\ ta /\ ( ph /\ ps /\ ch ) ) ) -> ps ) $=
    ( w3a simp32 3ad2ant3 ) DEABCHHFBGDEABCIJ $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simp333 $p |- ( ( et /\ ze /\ ( th /\ ta /\ ( ph /\ ps /\ ch ) ) ) -> ch ) $=
    ( w3a simp33 3ad2ant3 ) DEABCHHFCGDEABCIJ $.
    $( [9-Mar-2012] $)

  ${
    3adantl.1 $e |- ( ( ( ph /\ ps ) /\ ch ) -> th ) $.
    $( Deduction adding a conjunct to antecedent. $)
    3adantl1 $p |- ( ( ( ta /\ ph /\ ps ) /\ ch ) -> th ) $=
      ( w3a wa 3simpc sylan ) EABGABHCDEABIFJ $.
      $( [24-Feb-2005] $)

    $( Deduction adding a conjunct to antecedent. $)
    3adantl2 $p |- ( ( ( ph /\ ta /\ ps ) /\ ch ) -> th ) $=
      ( w3a wa 3simpb sylan ) AEBGABHCDAEBIFJ $.
      $( [24-Feb-2005] $)

    $( Deduction adding a conjunct to antecedent. $)
    3adantl3 $p |- ( ( ( ph /\ ps /\ ta ) /\ ch ) -> th ) $=
      ( w3a wa 3simpa sylan ) ABEGABHCDABEIFJ $.
      $( [24-Feb-2005] $)
  $}

  ${
    3adantr.1 $e |- ( ( ph /\ ( ps /\ ch ) ) -> th ) $.
    $( Deduction adding a conjunct to antecedent. $)
    3adantr1 $p |- ( ( ph /\ ( ta /\ ps /\ ch ) ) -> th ) $=
      ( w3a wa 3simpc sylan2 ) EBCGABCHDEBCIFJ $.
      $( [27-Apr-2005] $)

    $( Deduction adding a conjunct to antecedent. $)
    3adantr2 $p |- ( ( ph /\ ( ps /\ ta /\ ch ) ) -> th ) $=
      ( w3a wa 3simpb sylan2 ) BECGABCHDBECIFJ $.
      $( [27-Apr-2005] $)

    $( Deduction adding a conjunct to antecedent. $)
    3adantr3 $p |- ( ( ph /\ ( ps /\ ch /\ ta ) ) -> th ) $=
      ( w3a wa 3simpa sylan2 ) BCEGABCHDBCEIFJ $.
      $( [27-Apr-2005] $)
  $}

  ${
    3ad2antl.1 $e |- ( ( ph /\ ch ) -> th ) $.
    $( Deduction adding conjuncts to antecedent. $)
    3ad2antl1 $p |- ( ( ( ph /\ ps /\ ta ) /\ ch ) -> th ) $=
      ( adantlr 3adantl2 ) AECDBACDEFGH $.
      $( [4-Aug-2007] $)

    $( Deduction adding conjuncts to antecedent. $)
    3ad2antl2 $p |- ( ( ( ps /\ ph /\ ta ) /\ ch ) -> th ) $=
      ( adantlr 3adantl1 ) AECDBACDEFGH $.
      $( [4-Aug-2007] $)

    $( Deduction adding conjuncts to antecedent. $)
    3ad2antl3 $p |- ( ( ( ps /\ ta /\ ph ) /\ ch ) -> th ) $=
      ( adantll 3adantl1 ) EACDBACDEFGH $.
      $( [4-Aug-2007] $)

    $( Deduction adding a conjuncts to antecedent. $)
    3ad2antr1 $p |- ( ( ph /\ ( ch /\ ps /\ ta ) ) -> th ) $=
      ( adantrr 3adantr3 ) ACBDEACDBFGH $.
      $( [25-Dec-2007] $)

    $( Deduction adding a conjuncts to antecedent. $)
    3ad2antr2 $p |- ( ( ph /\ ( ps /\ ch /\ ta ) ) -> th ) $=
      ( adantrl 3adantr3 ) ABCDEACDBFGH $.
      $( [27-Dec-2007] $)

    $( Deduction adding a conjuncts to antecedent. $)
    3ad2antr3 $p |- ( ( ph /\ ( ps /\ ta /\ ch ) ) -> th ) $=
      ( adantrl 3adantr1 ) AECDBACDEFGH $.
      $( [30-Dec-2007] $)
  $}

  ${
    3anibar.1 $e |- ( ( ph /\ ps /\ ch ) -> ( th <-> ( ch /\ ta ) ) ) $.
    $( Remove a hypothesis from the second member of a biimplication.
       (Contributed by FL, 22-Jul-2008.) $)
    3anibar $p |- ( ( ph /\ ps /\ ch ) -> ( th <-> ta ) ) $=
      ( w3a wa simp3 biantrurd bitr4d ) ABCGZDCEHEFLCEABCIJK $.
      $( [2-Mar-2011] $) $( [14-Jul-2008] $)
  $}

  $( Introduction in triple disjunction. $)
  3mix1 $p |- ( ph -> ( ph \/ ps \/ ch ) ) $=
    ( wo w3o orc 3orass sylibr ) AABCDZDABCEAIFABCGH $.
    $( [4-Apr-1995] $)

  $( Introduction in triple disjunction. $)
  3mix2 $p |- ( ph -> ( ps \/ ph \/ ch ) ) $=
    ( w3o 3mix1 3orrot sylibr ) AACBDBACDACBEBACFG $.
    $( [4-Apr-1995] $)

  $( Introduction in triple disjunction. $)
  3mix3 $p |- ( ph -> ( ps \/ ch \/ ph ) ) $=
    ( w3o 3mix1 3orrot sylib ) AABCDBCADABCEABCFG $.
    $( [4-Apr-1995] $)

  ${
    3pm3.2i.1 $e |- ph $.
    3pm3.2i.2 $e |- ps $.
    3pm3.2i.3 $e |- ch $.
    $( Infer conjunction of premises. $)
    3pm3.2i $p |- ( ph /\ ps /\ ch ) $=
      ( w3a wa pm3.2i df-3an mpbir2an ) ABCGABHCABDEIFABCJK $.
      $( [10-Feb-1995] $)
  $}

  ${
    $( ~ pm3.2 for a triple conjunction.  (Contributed by Alan Sare,
       24-Oct-2011.) $)
    pm3.2an3 $p |- ( ph -> ( ps -> ( ch -> ( ph /\ ps /\ ch ) ) ) ) $=
      ( wa w3a wi pm3.2 ex df-3an bicomi syl8ib ) ABCABDZCDZABCEZABCMFLCGHNMABC
      IJK $.
      $( [24-Oct-2011] $)
  $}

  ${
    3jca.1 $e |- ( ph -> ps ) $.
    3jca.2 $e |- ( ph -> ch ) $.
    3jca.3 $e |- ( ph -> th ) $.
    $( Join consequents with conjunction. $)
    3jca $p |- ( ph -> ( ps /\ ch /\ th ) ) $=
      ( wa w3a jca31 df-3an sylibr ) ABCHDHBCDIABCDEFGJBCDKL $.
      $( [9-Apr-1994] $)
  $}

  ${
    3jcad.1 $e |- ( ph -> ( ps -> ch ) ) $.
    3jcad.2 $e |- ( ph -> ( ps -> th ) ) $.
    3jcad.3 $e |- ( ph -> ( ps -> ta ) ) $.
    $( Deduction conjoining the consequents of three implications. $)
    3jcad $p |- ( ph -> ( ps -> ( ch /\ th /\ ta ) ) ) $=
      ( w3a wa imp 3jca ex ) ABCDEIABJCDEABCFKABDGKABEHKLM $.
      $( [25-Sep-2005] $)
  $}

  ${
    mpbir3an.1 $e |- ps $.
    mpbir3an.2 $e |- ch $.
    mpbir3an.3 $e |- th $.
    mpbir3an.4 $e |- ( ph <-> ( ps /\ ch /\ th ) ) $.
    $( Detach a conjunction of truths in a biconditional. $)
    mpbir3an $p |- ph $=
      ( w3a 3pm3.2i mpbir ) ABCDIBCDEFGJHK $.
      $( [9-Jan-2015] $) $( [16-Sep-2011] $)
  $}

  ${
    mpbir3and.1 $e |- ( ph -> ch ) $.
    mpbir3and.2 $e |- ( ph -> th ) $.
    mpbir3and.3 $e |- ( ph -> ta ) $.
    mpbir3and.4 $e |- ( ph -> ( ps <-> ( ch /\ th /\ ta ) ) ) $.
    $( Detach a conjunction of truths in a biconditional.  (Contributed by
       Mario Carneiro, 11-May-2014.) $)
    mpbir3and $p |- ( ph -> ps ) $=
      ( w3a 3jca mpbird ) ABCDEJACDEFGHKIL $.
      $( [9-Jan-2015] $) $( [11-May-2014] $)
  $}

  ${
    mpbir3anOLD.1 $e |- ( ph <-> ( ps /\ ch /\ th ) ) $.
    mpbir3anOLD.2 $e |- ps $.
    mpbir3anOLD.3 $e |- ch $.
    mpbir3anOLD.4 $e |- th $.
    $( Obsolete version of ~ mpbir3an as of 9-Jan-2015. $)
    mpbir3anOLD $p |- ph $=
      ( mpbir3an ) ABCDFGHEI $.
      $( [16-Sep-2011] $)
  $}

  ${
    mpbir3andOLD.1 $e |- ( ph -> ( ps <-> ( ch /\ th /\ ta ) ) ) $.
    mpbir3andOLD.2 $e |- ( ph -> ch ) $.
    mpbir3andOLD.3 $e |- ( ph -> th ) $.
    mpbir3andOLD.4 $e |- ( ph -> ta ) $.
    $( Obsolete version of ~ mpbir3and as of 9-Jan-2015. $)
    mpbir3andOLD $p |- ( ph -> ps ) $=
      ( mpbir3and ) ABCDEGHIFJ $.
      $( [11-May-2014] $)
  $}

  ${
    syl3anbrc.1 $e |- ( ph -> ps ) $.
    syl3anbrc.2 $e |- ( ph -> ch ) $.
    syl3anbrc.3 $e |- ( ph -> th ) $.
    syl3anbrc.4 $e |- ( ta <-> ( ps /\ ch /\ th ) ) $.
    $( Syllogism inference.  (Contributed by Mario Carneiro, 11-May-2014.) $)
    syl3anbrc $p |- ( ph -> ta ) $=
      ( w3a 3jca sylibr ) ABCDJEABCDFGHKIL $.
      $( [11-May-2014] $)
  $}

  ${
    3anim123i.1 $e |- ( ph -> ps ) $.
    3anim123i.2 $e |- ( ch -> th ) $.
    3anim123i.3 $e |- ( ta -> et ) $.
    $( Join antecedents and consequents with conjunction. $)
    3anim123i $p |- ( ( ph /\ ch /\ ta ) -> ( ps /\ th /\ et ) ) $=
      ( w3a 3ad2ant1 3ad2ant2 3ad2ant3 3jca ) ACEJBDFACBEGKCADEHLEAFCIMN $.
      $( [8-Apr-1994] $)
  $}

  ${
    3animi.1 $e |- ( ph -> ps ) $.
    $( Add two conjuncts to antecedent and consequent.  (Contributed by Jeff
       Hankins, 16-Aug-2009.) $)
    3anim1i $p |- ( ( ph /\ ch /\ th ) -> ( ps /\ ch /\ th ) ) $=
      ( id 3anim123i ) ABCCDDECFDFG $.
      $( [21-Feb-2011] $) $( [16-Aug-2009] $)

    $( Add two conjuncts to antecedent and consequent.  (Contributed by Jeff
       Hankins, 19-Aug-2009.) $)
    3anim3i $p |- ( ( ch /\ th /\ ph ) -> ( ch /\ th /\ ps ) ) $=
      ( id 3anim123i ) CCDDABCFDFEG $.
      $( [21-Feb-2011] $) $( [16-Aug-2009] $)
  $}

  ${
    bi3.1 $e |- ( ph <-> ps ) $.
    bi3.2 $e |- ( ch <-> th ) $.
    bi3.3 $e |- ( ta <-> et ) $.
    $( Join 3 biconditionals with conjunction. $)
    3anbi123i $p |- ( ( ph /\ ch /\ ta ) <-> ( ps /\ th /\ et ) ) $=
      ( wa w3a anbi12i df-3an 3bitr4i ) ACJZEJBDJZFJACEKBDFKOPEFABCDGHLILACEMBD
      FMN $.
      $( [21-Apr-1994] $)

    $( Join 3 biconditionals with disjunction. $)
    3orbi123i $p |- ( ( ph \/ ch \/ ta ) <-> ( ps \/ th \/ et ) ) $=
      ( wo w3o orbi12i df-3or 3bitr4i ) ACJZEJBDJZFJACEKBDFKOPEFABCDGHLILACEMBD
      FMN $.
      $( [17-May-1994] $)
  $}

  ${
    3anbi1i.1 $e |- ( ph <-> ps ) $.
    $( Inference adding two conjuncts to each side of a biconditional. $)
    3anbi1i $p |- ( ( ph /\ ch /\ th ) <-> ( ps /\ ch /\ th ) ) $=
      ( biid 3anbi123i ) ABCCDDECFDFG $.
      $( [8-Sep-2006] $)

    $( Inference adding two conjuncts to each side of a biconditional. $)
    3anbi2i $p |- ( ( ch /\ ph /\ th ) <-> ( ch /\ ps /\ th ) ) $=
      ( biid 3anbi123i ) CCABDDCFEDFG $.
      $( [8-Sep-2006] $)

    $( Inference adding two conjuncts to each side of a biconditional. $)
    3anbi3i $p |- ( ( ch /\ th /\ ph ) <-> ( ch /\ th /\ ps ) ) $=
      ( biid 3anbi123i ) CCDDABCFDFEG $.
      $( [8-Sep-2006] $)
  $}

  ${
    3imp.1 $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
    $( Importation inference. $)
    3imp $p |- ( ( ph /\ ps /\ ch ) -> th ) $=
      ( w3a wa df-3an imp31 sylbi ) ABCFABGCGDABCHABCDEIJ $.
      $( [8-Apr-1994] $)
  $}

  ${
    3impa.1 $e |- ( ( ( ph /\ ps ) /\ ch ) -> th ) $.
    $( Importation from double to triple conjunction. $)
    3impa $p |- ( ( ph /\ ps /\ ch ) -> th ) $=
      ( exp31 3imp ) ABCDABCDEFG $.
      $( [20-Aug-1995] $)
  $}

  ${
    3impb.1 $e |- ( ( ph /\ ( ps /\ ch ) ) -> th ) $.
    $( Importation from double to triple conjunction. $)
    3impb $p |- ( ( ph /\ ps /\ ch ) -> th ) $=
      ( exp32 3imp ) ABCDABCDEFG $.
      $( [20-Aug-1995] $)
  $}

  ${
    3impia.1 $e |- ( ( ph /\ ps ) -> ( ch -> th ) ) $.
    $( Importation to triple conjunction. $)
    3impia $p |- ( ( ph /\ ps /\ ch ) -> th ) $=
      ( wi ex 3imp ) ABCDABCDFEGH $.
      $( [13-Jun-2006] $)
  $}

  ${
    3impib.1 $e |- ( ph -> ( ( ps /\ ch ) -> th ) ) $.
    $( Importation to triple conjunction. $)
    3impib $p |- ( ( ph /\ ps /\ ch ) -> th ) $=
      ( exp3a 3imp ) ABCDABCDEFG $.
      $( [13-Jun-2006] $)
  $}

  ${
    3exp.1 $e |- ( ( ph /\ ps /\ ch ) -> th ) $.
    $( Exportation inference. $)
    3exp $p |- ( ph -> ( ps -> ( ch -> th ) ) ) $=
      ( w3a pm3.2an3 syl8 ) ABCABCFDABCGEH $.
      $( [30-May-1994] $)

    $( Exportation from triple to double conjunction. $)
    3expa $p |- ( ( ( ph /\ ps ) /\ ch ) -> th ) $=
      ( 3exp imp31 ) ABCDABCDEFG $.
      $( [20-Aug-1995] $)

    $( Exportation from triple to double conjunction. $)
    3expb $p |- ( ( ph /\ ( ps /\ ch ) ) -> th ) $=
      ( 3exp imp32 ) ABCDABCDEFG $.
      $( [20-Aug-1995] $)

    $( Exportation from triple conjunction. $)
    3expia $p |- ( ( ph /\ ps ) -> ( ch -> th ) ) $=
      ( wi 3exp imp ) ABCDFABCDEGH $.
      $( [19-May-2007] $)

    $( Exportation from triple conjunction. $)
    3expib $p |- ( ph -> ( ( ps /\ ch ) -> th ) ) $=
      ( 3exp imp3a ) ABCDABCDEFG $.
      $( [19-May-2007] $)

    $( Commutation in antecedent.  Swap 1st and 3rd.  (The proof was shortened
       by Andrew Salmon, 13-May-2011.) $)
    3com12 $p |- ( ( ps /\ ph /\ ch ) -> th ) $=
      ( w3a 3ancoma sylbi ) BACFABCFDBACGEH $.
      $( [16-May-2011] $) $( [28-Jan-1996] $)

    $( Commutation in antecedent.  Swap 1st and 3rd. $)
    3com13 $p |- ( ( ch /\ ps /\ ph ) -> th ) $=
      ( w3a 3anrev sylbi ) CBAFABCFDCBAGEH $.
      $( [28-Jan-1996] $)

    $( Commutation in antecedent.  Swap 2nd and 3rd. $)
    3com23 $p |- ( ( ph /\ ch /\ ps ) -> th ) $=
      ( 3exp com23 3imp ) ACBDABCDABCDEFGH $.
      $( [28-Jan-1996] $)

    $( Commutation in antecedent.  Rotate left. $)
    3coml $p |- ( ( ps /\ ch /\ ph ) -> th ) $=
      ( 3com23 3com13 ) ACBDABCDEFG $.
      $( [28-Jan-1996] $)

    $( Commutation in antecedent.  Rotate right. $)
    3comr $p |- ( ( ch /\ ph /\ ps ) -> th ) $=
      ( 3coml ) BCADABCDEFF $.
      $( [28-Jan-1996] $)

    $( Deduction adding a conjunct to antecedent. $)
    3adant3r1 $p |- ( ( ph /\ ( ta /\ ps /\ ch ) ) -> th ) $=
      ( 3expb 3adantr1 ) ABCDEABCDFGH $.
      $( [16-Feb-2008] $)

    $( Deduction adding a conjunct to antecedent. $)
    3adant3r2 $p |- ( ( ph /\ ( ps /\ ta /\ ch ) ) -> th ) $=
      ( 3expb 3adantr2 ) ABCDEABCDFGH $.
      $( [17-Feb-2008] $)

    $( Deduction adding a conjunct to antecedent. $)
    3adant3r3 $p |- ( ( ph /\ ( ps /\ ch /\ ta ) ) -> th ) $=
      ( 3expb 3adantr3 ) ABCDEABCDFGH $.
      $( [18-Feb-2008] $)
  $}

  ${
    3an1rs.1 $e |- ( ( ( ph /\ ps /\ ch ) /\ th ) -> ta ) $.
    $( Swap conjuncts. $)
    3an1rs $p |- ( ( ( ph /\ ps /\ th ) /\ ch ) -> ta ) $=
      ( w3a wi ex 3exp com34 3imp imp ) ABDGCEABDCEHABCDEABCDEHABCGDEFIJKLM $.
      $( [16-Dec-2007] $)
  $}

  ${
    3imp1.1 $e |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ) $.
    $( Importation to left triple conjunction. $)
    3imp1 $p |- ( ( ( ph /\ ps /\ ch ) /\ th ) -> ta ) $=
      ( w3a wi 3imp imp ) ABCGDEABCDEHFIJ $.
      $( [24-Feb-2005] $)

    $( Importation deduction for triple conjunction. $)
    3impd $p |- ( ph -> ( ( ps /\ ch /\ th ) -> ta ) ) $=
      ( w3a wi com4l 3imp com12 ) BCDGAEBCDAEHABCDEFIJK $.
      $( [26-Oct-2006] $)

    $( Importation to right triple conjunction. $)
    3imp2 $p |- ( ( ph /\ ( ps /\ ch /\ th ) ) -> ta ) $=
      ( w3a 3impd imp ) ABCDGEABCDEFHI $.
      $( [26-Oct-2006] $)
  $}

  ${
    3exp1.1 $e |- ( ( ( ph /\ ps /\ ch ) /\ th ) -> ta ) $.
    $( Exportation from left triple conjunction. $)
    3exp1 $p |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ) $=
      ( wi w3a ex 3exp ) ABCDEGABCHDEFIJ $.
      $( [24-Feb-2005] $)
  $}

  ${
    3expd.1 $e |- ( ph -> ( ( ps /\ ch /\ th ) -> ta ) ) $.
    $( Exportation deduction for triple conjunction. $)
    3expd $p |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ) $=
      ( wi w3a com12 3exp com4r ) BCDAEBCDAEGABCDHEFIJK $.
      $( [26-Oct-2006] $)
  $}

  ${
    3exp2.1 $e |- ( ( ph /\ ( ps /\ ch /\ th ) ) -> ta ) $.
    $( Exportation from right triple conjunction. $)
    3exp2 $p |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ) $=
      ( w3a ex 3expd ) ABCDEABCDGEFHI $.
      $( [26-Oct-2006] $)
  $}

  ${
    exp5o.1 $e |- ( ( ph /\ ps /\ ch ) -> ( ( th /\ ta ) -> et ) ) $.
    $( A triple exportation inference.  (Contributed by Jeff Hankins,
       8-Jul-2009.) $)
    exp5o $p |- ( ph -> ( ps -> ( ch -> ( th -> ( ta -> et ) ) ) ) ) $=
      ( wi w3a exp3a 3exp ) ABCDEFHHABCIDEFGJK $.
      $( [8-Jul-2009] $)
  $}

  ${
    exp516.1 $e |- ( ( ( ph /\ ( ps /\ ch /\ th ) ) /\ ta ) -> et ) $.
    $( A triple exportation inference.  (Contributed by Jeff Hankins,
       8-Jul-2009.) $)
    exp516 $p |- ( ph -> ( ps -> ( ch -> ( th -> ( ta -> et ) ) ) ) ) $=
      ( wi w3a exp31 3expd ) ABCDEFHABCDIEFGJK $.
      $( [8-Jul-2009] $)
  $}

  ${
    exp520.1 $e |- ( ( ( ph /\ ps /\ ch ) /\ ( th /\ ta ) ) -> et ) $.
    $( A triple exportation inference.  (Contributed by Jeff Hankins,
       8-Jul-2009.) $)
    exp520 $p |- ( ph -> ( ps -> ( ch -> ( th -> ( ta -> et ) ) ) ) ) $=
      ( w3a wa ex exp5o ) ABCDEFABCHDEIFGJK $.
      $( [8-Jul-2009] $)
  $}

  ${
    3adant1l.1 $e |- ( ( ph /\ ps /\ ch ) -> th ) $.
    $( Deduction adding a conjunct to antecedent. $)
    3adant1l $p |- ( ( ( ta /\ ph ) /\ ps /\ ch ) -> th ) $=
      ( wa 3expb adantll 3impb ) EAGBCDABCGDEABCDFHIJ $.
      $( [8-Jan-2006] $)

    $( Deduction adding a conjunct to antecedent. $)
    3adant1r $p |- ( ( ( ph /\ ta ) /\ ps /\ ch ) -> th ) $=
      ( wa 3expb adantlr 3impb ) AEGBCDABCGDEABCDFHIJ $.
      $( [8-Jan-2006] $)

    $( Deduction adding a conjunct to antecedent. $)
    3adant2l $p |- ( ( ph /\ ( ta /\ ps ) /\ ch ) -> th ) $=
      ( wa 3com12 3adant1l ) EBGACDBACDEABCDFHIH $.
      $( [8-Jan-2006] $)

    $( Deduction adding a conjunct to antecedent. $)
    3adant2r $p |- ( ( ph /\ ( ps /\ ta ) /\ ch ) -> th ) $=
      ( wa 3com12 3adant1r ) BEGACDBACDEABCDFHIH $.
      $( [8-Jan-2006] $)

    $( Deduction adding a conjunct to antecedent. $)
    3adant3l $p |- ( ( ph /\ ps /\ ( ta /\ ch ) ) -> th ) $=
      ( wa 3com13 3adant1l ) ECGBADCBADEABCDFHIH $.
      $( [8-Jan-2006] $)

    $( Deduction adding a conjunct to antecedent. $)
    3adant3r $p |- ( ( ph /\ ps /\ ( ch /\ ta ) ) -> th ) $=
      ( wa 3com13 3adant1r ) CEGBADCBADEABCDFHIH $.
      $( [8-Jan-2006] $)
  $}

  ${
    sylXanc.1 $e |- ( ph -> ps ) $.
    sylXanc.2 $e |- ( ph -> ch ) $.
    sylXanc.3 $e |- ( ph -> th ) $.
    ${
      syl12anc.4 $e |- ( ( ps /\ ( ch /\ th ) ) -> ta ) $.
      $( Syllogism combined with contraction.  (Contributed by Jeff Hankins,
         1-Aug-2009.) $)
      syl12anc $p |- ( ph -> ta ) $=
        ( wa jca32 syl ) ABCDJJEABCDFGHKIL $.
        $( [1-Aug-2009] $)
    $}

    ${
      syl21anc.4 $e |- ( ( ( ps /\ ch ) /\ th ) -> ta ) $.
      $( Syllogism combined with contraction.  (Contributed by Jeff Hankins,
         1-Aug-2009.) $)
      syl21anc $p |- ( ph -> ta ) $=
        ( wa jca31 syl ) ABCJDJEABCDFGHKIL $.
        $( [1-Aug-2009] $)
    $}

    ${
      syl111anc.4 $e |- ( ( ps /\ ch /\ th ) -> ta ) $.
      $( Syllogism combined with contraction. $)
      syl3anc $p |- ( ph -> ta ) $=
        ( w3a 3jca syl ) ABCDJEABCDFGHKIL $.
        $( [11-Mar-2012] $)
    $}

    sylXanc.4 $e |- ( ph -> ta ) $.
    ${
      syl22anc.5 $e |- ( ( ( ps /\ ch ) /\ ( th /\ ta ) ) -> et ) $.
      $( Syllogism combined with contraction. $)
      syl22anc $p |- ( ph -> et ) $=
        ( wa jca syl12anc ) ABCLDEFABCGHMIJKN $.
        $( [11-Mar-2012] $)
    $}

    ${
      syl13anc.5 $e |- ( ( ps /\ ( ch /\ th /\ ta ) ) -> et ) $.
      $( Syllogism combined with contraction. $)
      syl13anc $p |- ( ph -> et ) $=
        ( w3a 3jca syl2anc ) ABCDELFGACDEHIJMKN $.
        $( [11-Mar-2012] $)
    $}

    ${
      syl31anc.5 $e |- ( ( ( ps /\ ch /\ th ) /\ ta ) -> et ) $.
      $( Syllogism combined with contraction. $)
      syl31anc $p |- ( ph -> et ) $=
        ( w3a 3jca syl2anc ) ABCDLEFABCDGHIMJKN $.
        $( [11-Mar-2012] $)
    $}

    ${
      syl112anc.5 $e |- ( ( ps /\ ch /\ ( th /\ ta ) ) -> et ) $.
      $( Syllogism combined with contraction. $)
      syl112anc $p |- ( ph -> et ) $=
        ( wa jca syl3anc ) ABCDELFGHADEIJMKN $.
        $( [11-Mar-2012] $)
    $}

    ${
      syl121anc.5 $e |- ( ( ps /\ ( ch /\ th ) /\ ta ) -> et ) $.
      $( Syllogism combined with contraction. $)
      syl121anc $p |- ( ph -> et ) $=
        ( wa jca syl3anc ) ABCDLEFGACDHIMJKN $.
        $( [11-Mar-2012] $)
    $}

    ${
      syl211anc.5 $e |- ( ( ( ps /\ ch ) /\ th /\ ta ) -> et ) $.
      $( Syllogism combined with contraction. $)
      syl211anc $p |- ( ph -> et ) $=
        ( wa jca syl3anc ) ABCLDEFABCGHMIJKN $.
        $( [11-Mar-2012] $)
    $}

    sylXanc.5 $e |- ( ph -> et ) $.
    ${
      syl23anc.6 $e |- ( ( ( ps /\ ch ) /\ ( th /\ ta /\ et ) ) -> ze ) $.
      $( Syllogism combined with contraction. $)
      syl23anc $p |- ( ph -> ze ) $=
        ( wa jca syl13anc ) ABCNDEFGABCHIOJKLMP $.
        $( [11-Mar-2012] $)
    $}

    ${
      syl32anc.6 $e |- ( ( ( ps /\ ch /\ th ) /\ ( ta /\ et ) ) -> ze ) $.
      $( Syllogism combined with contraction. $)
      syl32anc $p |- ( ph -> ze ) $=
        ( wa jca syl31anc ) ABCDEFNGHIJAEFKLOMP $.
        $( [11-Mar-2012] $)
    $}

    ${
      syl122anc.6 $e |- ( ( ps /\ ( ch /\ th ) /\ ( ta /\ et ) ) -> ze ) $.
      $( Syllogism combined with contraction. $)
      syl122anc $p |- ( ph -> ze ) $=
        ( wa jca syl121anc ) ABCDEFNGHIJAEFKLOMP $.
        $( [11-Mar-2012] $)
    $}

    ${
      syl212anc.6 $e |- ( ( ( ps /\ ch ) /\ th /\ ( ta /\ et ) ) -> ze ) $.
      $( Syllogism combined with contraction. $)
      syl212anc $p |- ( ph -> ze ) $=
        ( wa jca syl211anc ) ABCDEFNGHIJAEFKLOMP $.
        $( [11-Mar-2012] $)
    $}

    ${
      syl221anc.6 $e |- ( ( ( ps /\ ch ) /\ ( th /\ ta ) /\ et ) -> ze ) $.
      $( Syllogism combined with contraction. $)
      syl221anc $p |- ( ph -> ze ) $=
        ( wa jca syl211anc ) ABCDENFGHIADEJKOLMP $.
        $( [11-Mar-2012] $)
    $}

    ${
      syl113anc.6 $e |- ( ( ps /\ ch /\ ( th /\ ta /\ et ) ) -> ze ) $.
      $( Syllogism combined with contraction. $)
      syl113anc $p |- ( ph -> ze ) $=
        ( w3a 3jca syl3anc ) ABCDEFNGHIADEFJKLOMP $.
        $( [11-Mar-2012] $)
    $}

    ${
      syl131anc.6 $e |- ( ( ps /\ ( ch /\ th /\ ta ) /\ et ) -> ze ) $.
      $( Syllogism combined with contraction. $)
      syl131anc $p |- ( ph -> ze ) $=
        ( w3a 3jca syl3anc ) ABCDENFGHACDEIJKOLMP $.
        $( [11-Mar-2012] $)
    $}

    ${
      syl311anc.6 $e |- ( ( ( ps /\ ch /\ th ) /\ ta /\ et ) -> ze ) $.
      $( Syllogism combined with contraction. $)
      syl311anc $p |- ( ph -> ze ) $=
        ( w3a 3jca syl3anc ) ABCDNEFGABCDHIJOKLMP $.
        $( [11-Mar-2012] $)
    $}

    sylXanc.6 $e |- ( ph -> ze ) $.
    ${
      syl33anc.7 $e |- ( ( ( ps /\ ch /\ th ) /\ ( ta /\ et /\ ze ) )
           -> si ) $.
      $( Syllogism combined with contraction. $)
      syl33anc $p |- ( ph -> si ) $=
        ( w3a 3jca syl13anc ) ABCDPEFGHABCDIJKQLMNOR $.
        $( [11-Mar-2012] $)
    $}

    ${
      syl222anc.7 $e |- ( ( ( ps /\ ch ) /\ ( th /\ ta ) /\ ( et /\ ze ) )
           -> si ) $.
      $( Syllogism combined with contraction. $)
      syl222anc $p |- ( ph -> si ) $=
        ( wa jca syl221anc ) ABCDEFGPHIJKLAFGMNQOR $.
        $( [11-Mar-2012] $)
    $}

    ${
      syl123anc.7 $e |- ( ( ps /\ ( ch /\ th ) /\ ( ta /\ et /\ ze ) )
           -> si ) $.
      $( Syllogism combined with contraction. $)
      syl123anc $p |- ( ph -> si ) $=
        ( wa jca syl113anc ) ABCDPEFGHIACDJKQLMNOR $.
        $( [11-Mar-2012] $)
    $}

    ${
      syl132anc.7 $e |- ( ( ps /\ ( ch /\ th /\ ta ) /\ ( et /\ ze ) )
           -> si ) $.
      $( Syllogism combined with contraction. $)
      syl132anc $p |- ( ph -> si ) $=
        ( wa jca syl131anc ) ABCDEFGPHIJKLAFGMNQOR $.
        $( [11-Jul-2012] $)
    $}

    ${
      syl213anc.7 $e |- ( ( ( ps /\ ch ) /\ th /\ ( ta /\ et /\ ze ) )
           -> si ) $.
      $( Syllogism combined with contraction. $)
      syl213anc $p |- ( ph -> si ) $=
        ( wa jca syl113anc ) ABCPDEFGHABCIJQKLMNOR $.
        $( [11-Mar-2012] $)
    $}

    ${
      syl231anc.7 $e |- ( ( ( ps /\ ch ) /\ ( th /\ ta /\ et ) /\ ze )
           -> si ) $.
      $( Syllogism combined with contraction. $)
      syl231anc $p |- ( ph -> si ) $=
        ( wa jca syl131anc ) ABCPDEFGHABCIJQKLMNOR $.
        $( [11-Mar-2012] $)
    $}

    ${
      syl312anc.7 $e |- ( ( ( ps /\ ch /\ th ) /\ ta /\ ( et /\ ze ) )
           -> si ) $.
      $( Syllogism combined with contraction. $)
      syl312anc $p |- ( ph -> si ) $=
        ( wa jca syl311anc ) ABCDEFGPHIJKLAFGMNQOR $.
        $( [11-Jul-2012] $)
    $}

    ${
      syl321anc.7 $e |- ( ( ( ps /\ ch /\ th ) /\ ( ta /\ et ) /\ ze )
           -> si ) $.
      $( Syllogism combined with contraction. $)
      syl321anc $p |- ( ph -> si ) $=
        ( wa jca syl311anc ) ABCDEFPGHIJKAEFLMQNOR $.
        $( [11-Jul-2012] $)
    $}

    sylXanc.7 $e |- ( ph -> si ) $.
    ${
      syl133anc.8 $e |- ( ( ps /\ ( ch /\ th /\ ta ) /\ ( et /\ ze /\ si ) )
           -> rh ) $.
      $( Syllogism combined with contraction. $)
      syl133anc $p |- ( ph -> rh ) $=
        ( w3a 3jca syl131anc ) ABCDEFGHRIJKLMAFGHNOPSQT $.
        $( [11-Mar-2012] $)
    $}

    ${
      syl313anc.8 $e |- ( ( ( ps /\ ch /\ th ) /\ ta /\ ( et /\ ze /\ si ) )
           -> rh ) $.
      $( Syllogism combined with contraction. $)
      syl313anc $p |- ( ph -> rh ) $=
        ( w3a 3jca syl311anc ) ABCDEFGHRIJKLMAFGHNOPSQT $.
        $( [11-Mar-2012] $)
    $}

    ${
      syl331anc.8 $e |- ( ( ( ps /\ ch /\ th ) /\ ( ta /\ et /\ ze ) /\ si )
           -> rh ) $.
      $( Syllogism combined with contraction. $)
      syl331anc $p |- ( ph -> rh ) $=
        ( w3a 3jca syl311anc ) ABCDEFGRHIJKLAEFGMNOSPQT $.
        $( [11-Mar-2012] $)
    $}

    ${
      syl223anc.8 $e |- ( ( ( ps /\ ch ) /\ ( th /\ ta ) /\ ( et /\ ze /\ si )
          ) -> rh ) $.
      $( Syllogism combined with contraction. $)
      syl223anc $p |- ( ph -> rh ) $=
        ( wa jca syl213anc ) ABCDERFGHIJKADELMSNOPQT $.
        $( [11-Mar-2012] $)
    $}

    ${
      syl232anc.8 $e |- ( ( ( ps /\ ch ) /\ ( th /\ ta /\ et ) /\ ( ze /\ si )
          ) -> rh ) $.
      $( Syllogism combined with contraction. $)
      syl232anc $p |- ( ph -> rh ) $=
        ( wa jca syl231anc ) ABCDEFGHRIJKLMNAGHOPSQT $.
        $( [11-Mar-2012] $)
    $}

    ${
      syl322anc.8 $e |- ( ( ( ps /\ ch /\ th ) /\ ( ta /\ et ) /\ ( ze /\ si )
          ) -> rh ) $.
      $( Syllogism combined with contraction. $)
      syl322anc $p |- ( ph -> rh ) $=
        ( wa jca syl321anc ) ABCDEFGHRIJKLMNAGHOPSQT $.
        $( [11-Mar-2012] $)
    $}

    sylXanc.8 $e |- ( ph -> rh ) $.
    ${
      syl233anc.9 $e |- ( ( ( ps /\ ch ) /\ ( th /\ ta /\ et ) /\ ( ze /\ si /\
          rh ) ) -> mu ) $.
      $( Syllogism combined with contraction. $)
      syl233anc $p |- ( ph -> mu ) $=
        ( wa jca syl133anc ) ABCTDEFGHIJABCKLUAMNOPQRSUB $.
        $( [11-Mar-2012] $)
    $}

    ${
      syl323anc.9 $e |- ( ( ( ps /\ ch /\ th ) /\ ( ta /\ et ) /\ ( ze /\ si /\
          rh ) ) -> mu ) $.
      $( Syllogism combined with contraction. $)
      syl323anc $p |- ( ph -> mu ) $=
        ( wa jca syl313anc ) ABCDEFTGHIJKLMAEFNOUAPQRSUB $.
        $( [11-Mar-2012] $)
    $}

    ${
      syl332anc.9 $e |- ( ( ( ps /\ ch /\ th ) /\ ( ta /\ et /\ ze ) /\ ( si /\
          rh ) ) -> mu ) $.
      $( Syllogism combined with contraction. $)
      syl332anc $p |- ( ph -> mu ) $=
        ( wa jca syl331anc ) ABCDEFGHITJKLMNOPAHIQRUASUB $.
        $( [11-Mar-2012] $)
    $}

    sylXanc.9 $e |- ( ph -> mu ) $.
    ${
      syl333anc.10 $e |- ( ( ( ps /\ ch /\ th ) /\ ( ta /\ et /\ ze )
          /\ ( si /\ rh /\ mu ) ) -> la ) $.
      $( A syllogism inference combined with contraction. $)
      syl333anc $p |- ( ph -> la ) $=
        ( w3a 3jca syl331anc ) ABCDEFGHIJUBKLMNOPQAHIJRSTUCUAUD $.
        $( [10-Mar-2012] $)
    $}
  $}

  ${
    syl3an1.1 $e |- ( ph -> ps ) $.
    syl3an1.2 $e |- ( ( ps /\ ch /\ th ) -> ta ) $.
    $( A syllogism inference. $)
    syl3an1 $p |- ( ( ph /\ ch /\ th ) -> ta ) $=
      ( w3a 3anim1i syl ) ACDHBCDHEABCDFIGJ $.
      $( [22-Aug-1995] $)
  $}

  ${
    syl3an2.1 $e |- ( ph -> ch ) $.
    syl3an2.2 $e |- ( ( ps /\ ch /\ th ) -> ta ) $.
    $( A syllogism inference. $)
    syl3an2 $p |- ( ( ps /\ ph /\ th ) -> ta ) $=
      ( wi 3exp syl5 3imp ) BADEACBDEHFBCDEGIJK $.
      $( [22-Aug-1995] $)
  $}

  ${
    syl3an3.1 $e |- ( ph -> th ) $.
    syl3an3.2 $e |- ( ( ps /\ ch /\ th ) -> ta ) $.
    $( A syllogism inference. $)
    syl3an3 $p |- ( ( ps /\ ch /\ ph ) -> ta ) $=
      ( 3exp syl7 3imp ) BCAEADBCEFBCDEGHIJ $.
      $( [22-Aug-1995] $)
  $}

  ${
    syl3an1b.1 $e |- ( ph <-> ps ) $.
    syl3an1b.2 $e |- ( ( ps /\ ch /\ th ) -> ta ) $.
    $( A syllogism inference. $)
    syl3an1b $p |- ( ( ph /\ ch /\ th ) -> ta ) $=
      ( biimpi syl3an1 ) ABCDEABFHGI $.
      $( [22-Aug-1995] $)
  $}

  ${
    syl3an2b.1 $e |- ( ph <-> ch ) $.
    syl3an2b.2 $e |- ( ( ps /\ ch /\ th ) -> ta ) $.
    $( A syllogism inference. $)
    syl3an2b $p |- ( ( ps /\ ph /\ th ) -> ta ) $=
      ( biimpi syl3an2 ) ABCDEACFHGI $.
      $( [22-Aug-1995] $)
  $}

  ${
    syl3an3b.1 $e |- ( ph <-> th ) $.
    syl3an3b.2 $e |- ( ( ps /\ ch /\ th ) -> ta ) $.
    $( A syllogism inference. $)
    syl3an3b $p |- ( ( ps /\ ch /\ ph ) -> ta ) $=
      ( biimpi syl3an3 ) ABCDEADFHGI $.
      $( [22-Aug-1995] $)
  $}

  ${
    syl3an1br.1 $e |- ( ps <-> ph ) $.
    syl3an1br.2 $e |- ( ( ps /\ ch /\ th ) -> ta ) $.
    $( A syllogism inference. $)
    syl3an1br $p |- ( ( ph /\ ch /\ th ) -> ta ) $=
      ( biimpri syl3an1 ) ABCDEBAFHGI $.
      $( [22-Aug-1995] $)
  $}

  ${
    syl3an2br.1 $e |- ( ch <-> ph ) $.
    syl3an2br.2 $e |- ( ( ps /\ ch /\ th ) -> ta ) $.
    $( A syllogism inference. $)
    syl3an2br $p |- ( ( ps /\ ph /\ th ) -> ta ) $=
      ( biimpri syl3an2 ) ABCDECAFHGI $.
      $( [22-Aug-1995] $)
  $}

  ${
    syl3an3br.1 $e |- ( th <-> ph ) $.
    syl3an3br.2 $e |- ( ( ps /\ ch /\ th ) -> ta ) $.
    $( A syllogism inference. $)
    syl3an3br $p |- ( ( ps /\ ch /\ ph ) -> ta ) $=
      ( biimpri syl3an3 ) ABCDEDAFHGI $.
      $( [22-Aug-1995] $)
  $}

  ${
    syl3an.1 $e |- ( ph -> ps ) $.
    syl3an.2 $e |- ( ch -> th ) $.
    syl3an.3 $e |- ( ta -> et ) $.
    syl3an.4 $e |- ( ( ps /\ th /\ et ) -> ze ) $.
    $( A triple syllogism inference. $)
    syl3an $p |- ( ( ph /\ ch /\ ta ) -> ze ) $=
      ( w3a 3anim123i syl ) ACELBDFLGABCDEFHIJMKN $.
      $( [13-May-2004] $)
  $}

  ${
    syl3anb.1 $e |- ( ph <-> ps ) $.
    syl3anb.2 $e |- ( ch <-> th ) $.
    syl3anb.3 $e |- ( ta <-> et ) $.
    syl3anb.4 $e |- ( ( ps /\ th /\ et ) -> ze ) $.
    $( A triple syllogism inference. $)
    syl3anb $p |- ( ( ph /\ ch /\ ta ) -> ze ) $=
      ( w3a 3anbi123i sylbi ) ACELBDFLGABCDEFHIJMKN $.
      $( [15-Oct-2005] $)
  $}

  ${
    syl3anbr.1 $e |- ( ps <-> ph ) $.
    syl3anbr.2 $e |- ( th <-> ch ) $.
    syl3anbr.3 $e |- ( et <-> ta ) $.
    syl3anbr.4 $e |- ( ( ps /\ th /\ et ) -> ze ) $.
    $( A triple syllogism inference. $)
    syl3anbr $p |- ( ( ph /\ ch /\ ta ) -> ze ) $=
      ( bicomi syl3anb ) ABCDEFGBAHLDCILFEJLKM $.
      $( [29-Dec-2011] $)
  $}

  ${
    syld3an3.1 $e |- ( ( ph /\ ps /\ ch ) -> th ) $.
    syld3an3.2 $e |- ( ( ph /\ ps /\ th ) -> ta ) $.
    $( A syllogism inference. $)
    syld3an3 $p |- ( ( ph /\ ps /\ ch ) -> ta ) $=
      ( w3a simp1 simp2 syl3anc ) ABCHABDEABCIABCJFGK $.
      $( [20-May-2007] $)
  $}

  ${
    syld3an1.1 $e |- ( ( ch /\ ps /\ th ) -> ph ) $.
    syld3an1.2 $e |- ( ( ph /\ ps /\ th ) -> ta ) $.
    $( A syllogism inference. $)
    syld3an1 $p |- ( ( ch /\ ps /\ th ) -> ta ) $=
      ( 3com13 syld3an3 ) DBCEDBCAECBDAFHABDEGHIH $.
      $( [7-Jul-2008] $)
  $}

  ${
    syld3an2.1 $e |- ( ( ph /\ ch /\ th ) -> ps ) $.
    syld3an2.2 $e |- ( ( ph /\ ps /\ th ) -> ta ) $.
    $( A syllogism inference. $)
    syld3an2 $p |- ( ( ph /\ ch /\ th ) -> ta ) $=
      ( 3com23 syld3an3 ) ADCEADCBEACDBFHABDEGHIH $.
      $( [20-May-2007] $)
  $}

  ${
    syl3anl1.1 $e |- ( ph -> ps ) $.
    syl3anl1.2 $e |- ( ( ( ps /\ ch /\ th ) /\ ta ) -> et ) $.
    $( A syllogism inference. $)
    syl3anl1 $p |- ( ( ( ph /\ ch /\ th ) /\ ta ) -> et ) $=
      ( w3a 3anim1i sylan ) ACDIBCDIEFABCDGJHK $.
      $( [24-Feb-2005] $)
  $}

  ${
    syl3anl2.1 $e |- ( ph -> ch ) $.
    syl3anl2.2 $e |- ( ( ( ps /\ ch /\ th ) /\ ta ) -> et ) $.
    $( A syllogism inference. $)
    syl3anl2 $p |- ( ( ( ps /\ ph /\ th ) /\ ta ) -> et ) $=
      ( w3a wi ex syl3an2 imp ) BADIEFABCDEFJGBCDIEFHKLM $.
      $( [24-Feb-2005] $)
  $}

  ${
    syl3anl3.1 $e |- ( ph -> th ) $.
    syl3anl3.2 $e |- ( ( ( ps /\ ch /\ th ) /\ ta ) -> et ) $.
    $( A syllogism inference. $)
    syl3anl3 $p |- ( ( ( ps /\ ch /\ ph ) /\ ta ) -> et ) $=
      ( w3a 3anim3i sylan ) BCAIBCDIEFADBCGJHK $.
      $( [24-Feb-2005] $)
  $}

  ${
    syl3anl.1 $e |- ( ph -> ps ) $.
    syl3anl.2 $e |- ( ch -> th ) $.
    syl3anl.3 $e |- ( ta -> et ) $.
    syl3anl.4 $e |- ( ( ( ps /\ th /\ et ) /\ ze ) -> si ) $.
    $( A triple syllogism inference. $)
    syl3anl $p |- ( ( ( ph /\ ch /\ ta ) /\ ze ) -> si ) $=
      ( w3a 3anim123i sylan ) ACEMBDFMGHABCDEFIJKNLO $.
      $( [24-Dec-2006] $)
  $}

  ${
    syl3anr1.1 $e |- ( ph -> ps ) $.
    syl3anr1.2 $e |- ( ( ch /\ ( ps /\ th /\ ta ) ) -> et ) $.
    $( A syllogism inference. $)
    syl3anr1 $p |- ( ( ch /\ ( ph /\ th /\ ta ) ) -> et ) $=
      ( w3a 3anim1i sylan2 ) ADEICBDEIFABDEGJHK $.
      $( [31-Jul-2007] $)
  $}

  ${
    syl3anr2.1 $e |- ( ph -> th ) $.
    syl3anr2.2 $e |- ( ( ch /\ ( ps /\ th /\ ta ) ) -> et ) $.
    $( A syllogism inference. $)
    syl3anr2 $p |- ( ( ch /\ ( ps /\ ph /\ ta ) ) -> et ) $=
      ( w3a ancoms syl3anl2 ) BAEICFABDECFGCBDEIFHJKJ $.
      $( [1-Aug-2007] $)
  $}

  ${
    syl3anr3.1 $e |- ( ph -> ta ) $.
    syl3anr3.2 $e |- ( ( ch /\ ( ps /\ th /\ ta ) ) -> et ) $.
    $( A syllogism inference. $)
    syl3anr3 $p |- ( ( ch /\ ( ps /\ th /\ ph ) ) -> et ) $=
      ( w3a 3anim3i sylan2 ) BDAICBDEIFAEBDGJHK $.
      $( [23-Aug-2007] $)
  $}

  ${
    3impdi.1 $e |- ( ( ( ph /\ ps ) /\ ( ph /\ ch ) ) -> th ) $.
    $( Importation inference (undistribute conjunction). $)
    3impdi $p |- ( ( ph /\ ps /\ ch ) -> th ) $=
      ( anandis 3impb ) ABCDABCDEFG $.
      $( [14-Aug-1995] $)
  $}

  ${
    3impdir.1 $e |- ( ( ( ph /\ ps ) /\ ( ch /\ ps ) ) -> th ) $.
    $( Importation inference (undistribute conjunction). $)
    3impdir $p |- ( ( ph /\ ch /\ ps ) -> th ) $=
      ( anandirs 3impa ) ACBDACBDEFG $.
      $( [20-Aug-1995] $)
  $}

  ${
    3anidm12.1 $e |- ( ( ph /\ ph /\ ps ) -> ch ) $.
    $( Inference from idempotent law for conjunction. $)
    3anidm12 $p |- ( ( ph /\ ps ) -> ch ) $=
      ( 3expib anabsi5 ) ABCAABCDEF $.
      $( [7-Mar-2008] $)
  $}

  ${
    3anidm13.1 $e |- ( ( ph /\ ps /\ ph ) -> ch ) $.
    $( Inference from idempotent law for conjunction. $)
    3anidm13 $p |- ( ( ph /\ ps ) -> ch ) $=
      ( 3com23 3anidm12 ) ABCABACDEF $.
      $( [7-Mar-2008] $)
  $}

  ${
    3anidm23.1 $e |- ( ( ph /\ ps /\ ps ) -> ch ) $.
    $( Inference from idempotent law for conjunction. $)
    3anidm23 $p |- ( ( ph /\ ps ) -> ch ) $=
      ( 3expa anabss3 ) ABCABBCDEF $.
      $( [1-Feb-2007] $)
  $}

  ${
    3ori.1 $e |- ( ph \/ ps \/ ch ) $.
    $( Infer implication from triple disjunction. $)
    3ori $p |- ( ( -. ph /\ -. ps ) -> ch ) $=
      ( wn wa wo ioran w3o df-3or mpbi ori sylbir ) AEBEFABGZECABHNCABCINCGDABC
      JKLM $.
      $( [26-Sep-2006] $)
  $}

  $( Disjunction of 3 antecedents. $)
  3jao $p |- ( ( ( ph -> ps ) /\ ( ch -> ps ) /\ ( th -> ps ) ) ->
              ( ( ph \/ ch \/ th ) -> ps ) ) $=
    ( w3o wo wi w3a df-3or jao syl6 3imp syl5bi ) ACDEACFZDFZABGZCBGZDBGZHBACDI
    PQROBGZPQNBGRSGABCJNBDJKLM $.
    $( [8-Apr-1994] $)

  $( Disjunction of 3 antecedents. $)
  3jaob $p |- ( ( ( ph \/ ch \/ th ) -> ps ) <->
              ( ( ph -> ps ) /\ ( ch -> ps ) /\ ( th -> ps ) ) ) $=
    ( w3o wi w3a 3mix1 imim1i 3mix2 3mix3 3jca 3jao impbii ) ACDEZBFZABFZCBFZDB
    FZGPQRSAOBACDHICOBCADJIDOBDACKILABCDMN $.
    $( [13-Sep-2011] $)

  ${
    3jaoi.1 $e |- ( ph -> ps ) $.
    3jaoi.2 $e |- ( ch -> ps ) $.
    3jaoi.3 $e |- ( th -> ps ) $.
    $( Disjunction of 3 antecedents (inference). $)
    3jaoi $p |- ( ( ph \/ ch \/ th ) -> ps ) $=
      ( wi w3a w3o 3pm3.2i 3jao ax-mp ) ABHZCBHZDBHZIACDJBHNOPEFGKABCDLM $.
      $( [12-Sep-1995] $)
  $}

  ${
    3jaod.1 $e |- ( ph -> ( ps -> ch ) ) $.
    3jaod.2 $e |- ( ph -> ( th -> ch ) ) $.
    3jaod.3 $e |- ( ph -> ( ta -> ch ) ) $.
    $( Disjunction of 3 antecedents (deduction). $)
    3jaod $p |- ( ph -> ( ( ps \/ th \/ ta ) -> ch ) ) $=
      ( wi w3o 3jao syl3anc ) ABCIDCIECIBDEJCIFGHBCDEKL $.
      $( [14-Oct-2005] $)
  $}

  ${
    3jaoian.1 $e |- ( ( ph /\ ps ) -> ch ) $.
    3jaoian.2 $e |- ( ( th /\ ps ) -> ch ) $.
    3jaoian.3 $e |- ( ( ta /\ ps ) -> ch ) $.
    $( Disjunction of 3 antecedents (inference). $)
    3jaoian $p |- ( ( ( ph \/ th \/ ta ) /\ ps ) -> ch ) $=
      ( w3o wi ex 3jaoi imp ) ADEIBCABCJDEABCFKDBCGKEBCHKLM $.
      $( [14-Oct-2005] $)
  $}

  ${
    3jaodan.1 $e |- ( ( ph /\ ps ) -> ch ) $.
    3jaodan.2 $e |- ( ( ph /\ th ) -> ch ) $.
    3jaodan.3 $e |- ( ( ph /\ ta ) -> ch ) $.
    $( Disjunction of 3 antecedents (deduction). $)
    3jaodan $p |- ( ( ph /\ ( ps \/ th \/ ta ) ) -> ch ) $=
      ( w3o ex 3jaod imp ) ABDEICABCDEABCFJADCGJAECHJKL $.
      $( [14-Oct-2005] $)
  $}

  ${
    3jaao.1 $e |- ( ph -> ( ps -> ch ) ) $.
    3jaao.2 $e |- ( th -> ( ta -> ch ) ) $.
    3jaao.3 $e |- ( et -> ( ze -> ch ) ) $.
    $( Inference conjoining and disjoining the antecedents of three
       implications.  (Contributed by Jeff Hankins, 15-Aug-2009.)  (The proof
       was shortened by Andrew Salmon, 13-May-2011.) $)
    3jaao $p |- ( ( ph /\ th /\ et ) -> ( ( ps \/ ta \/ ze ) -> ch ) ) $=
      ( w3a wi 3ad2ant1 3ad2ant2 3ad2ant3 3jaod ) ADFKBCEGADBCLFHMDAECLFINFAGCL
      DJOP $.
      $( [16-May-2011] $) $( [3-Aug-2009] $)
  $}

  ${
    syl3an9b.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    syl3an9b.2 $e |- ( th -> ( ch <-> ta ) ) $.
    syl3an9b.3 $e |- ( et -> ( ta <-> ze ) ) $.
    $( Nested syllogism inference conjoining 3 dissimilar antecedents. $)
    syl3an9b $p |- ( ( ph /\ th /\ et ) -> ( ps <-> ze ) ) $=
      ( wb wa sylan9bb 3impa ) ADFBGKADLBEFGABCDEHIMJMN $.
      $( [1-May-1995] $)
  $}

  ${
    bi3d.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    bi3d.2 $e |- ( ph -> ( th <-> ta ) ) $.
    bi3d.3 $e |- ( ph -> ( et <-> ze ) ) $.
    $( Deduction joining 3 equivalences to form equivalence of disjunctions. $)
    3orbi123d $p |- ( ph -> ( ( ps \/ th \/ et ) <-> ( ch \/ ta \/ ze ) ) ) $=
      ( wo w3o orbi12d df-3or 3bitr4g ) ABDKZFKCEKZGKBDFLCEGLAPQFGABCDEHIMJMBDF
      NCEGNO $.
      $( [20-Apr-1994] $)

    $( Deduction joining 3 equivalences to form equivalence of conjunctions. $)
    3anbi123d $p |- ( ph -> ( ( ps /\ th /\ et ) <-> ( ch /\ ta /\ ze ) ) ) $=
      ( wa w3a anbi12d df-3an 3bitr4g ) ABDKZFKCEKZGKBDFLCEGLAPQFGABCDEHIMJMBDF
      NCEGNO $.
      $( [22-Apr-1994] $)
  $}

  ${
    3anbi12d.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    3anbi12d.2 $e |- ( ph -> ( th <-> ta ) ) $.
    $( Deduction conjoining and adding a conjunct to equivalences. $)
    3anbi12d $p |- ( ph -> ( ( ps /\ th /\ et ) <-> ( ch /\ ta /\ et ) ) ) $=
      ( biidd 3anbi123d ) ABCDEFFGHAFIJ $.
      $( [8-Sep-2006] $)

    $( Deduction conjoining and adding a conjunct to equivalences. $)
    3anbi13d $p |- ( ph -> ( ( ps /\ et /\ th ) <-> ( ch /\ et /\ ta ) ) ) $=
      ( biidd 3anbi123d ) ABCFFDEGAFIHJ $.
      $( [8-Sep-2006] $)

    $( Deduction conjoining and adding a conjunct to equivalences. $)
    3anbi23d $p |- ( ph -> ( ( et /\ ps /\ th ) <-> ( et /\ ch /\ ta ) ) ) $=
      ( biidd 3anbi123d ) AFFBCDEAFIGHJ $.
      $( [8-Sep-2006] $)
  $}

  ${
    3anbi1d.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Deduction adding conjuncts to an equivalence. $)
    3anbi1d $p |- ( ph -> ( ( ps /\ th /\ ta ) <-> ( ch /\ th /\ ta ) ) ) $=
      ( biidd 3anbi12d ) ABCDDEFADGH $.
      $( [8-Sep-2006] $)

    $( Deduction adding conjuncts to an equivalence. $)
    3anbi2d $p |- ( ph -> ( ( th /\ ps /\ ta ) <-> ( th /\ ch /\ ta ) ) ) $=
      ( biidd 3anbi12d ) ADDBCEADGFH $.
      $( [8-Sep-2006] $)

    $( Deduction adding conjuncts to an equivalence. $)
    3anbi3d $p |- ( ph -> ( ( th /\ ta /\ ps ) <-> ( th /\ ta /\ ch ) ) ) $=
      ( biidd 3anbi13d ) ADDBCEADGFH $.
      $( [8-Sep-2006] $)
  $}

  ${
    3anim123d.1 $e |- ( ph -> ( ps -> ch ) ) $.
    3anim123d.2 $e |- ( ph -> ( th -> ta ) ) $.
    3anim123d.3 $e |- ( ph -> ( et -> ze ) ) $.
    $( Deduction joining 3 implications to form implication of conjunctions. $)
    3anim123d $p |- ( ph -> ( ( ps /\ th /\ et ) -> ( ch /\ ta /\ ze ) ) ) $=
      ( wa w3a anim12d df-3an 3imtr4g ) ABDKZFKCEKZGKBDFLCEGLAPQFGABCDEHIMJMBDF
      NCEGNO $.
      $( [24-Feb-2005] $)

    $( Deduction joining 3 implications to form implication of disjunctions. $)
    3orim123d $p |- ( ph -> ( ( ps \/ th \/ et ) -> ( ch \/ ta \/ ze ) ) ) $=
      ( wo w3o orim12d df-3or 3imtr4g ) ABDKZFKCEKZGKBDFLCEGLAPQFGABCDEHIMJMBDF
      NCEGNO $.
      $( [4-Apr-1997] $)
  $}

  $( Rearrangement of 6 conjuncts. $)
  an6 $p |- ( ( ( ph /\ ps /\ ch ) /\ ( th /\ ta /\ et ) ) <->
              ( ( ph /\ th ) /\ ( ps /\ ta ) /\ ( ch /\ et ) ) ) $=
    ( w3a wa df-3an anbi12i an4 anbi1i 3bitri bitr4i ) ABCGZDEFGZHZADHZBEHZHZCF
    HZHZRSUAGQABHZCHZDEHZFHZHUCUEHZUAHUBOUDPUFABCIDEFIJUCCUEFKUGTUAABDEKLMRSUAI
    N $.
    $( [13-Mar-1995] $)

  $( Analog of ~ an4 for triple conjunction.  (Contributed by Scott Fenton,
     16-Mar-2011.)  (The proof was shortened by Andrew Salmon, 25-May-2011.) $)
  3an6 $p |- ( ( ( ph /\ ps ) /\ ( ch /\ th ) /\ ( ta /\ et ) ) <->
                ( ( ph /\ ch /\ ta ) /\ ( ps /\ th /\ et ) ) ) $=
    ( w3a wa an6 bicomi ) ACEGBDFGHABHCDHEFHGACEBDFIJ $.
    $( [25-May-2011] $) $( [16-Mar-2011] $)

  $( Analog of ~ or4 for triple conjunction.  (Contributed by Scott Fenton,
     16-Mar-2011.) $)
  3or6 $p |- ( ( ( ph \/ ps ) \/ ( ch \/ th ) \/ ( ta \/ et ) ) <->
                ( ( ph \/ ch \/ ta ) \/ ( ps \/ th \/ et ) ) ) $=
    ( wo w3o or4 orbi1i bitr2i df-3or orbi12i 3bitr4i ) ABGZCDGZGZEFGZGZACGZEGZ
    BDGZFGZGZOPRHACEHZBDFHZGUDTUBGZRGSTEUBFIUGQRACBDIJKOPRLUEUAUFUCACELBDFLMN
    $.
    $( [20-Mar-2011] $)

  ${
    mp3an1.1 $e |- ph $.
    mp3an1.2 $e |- ( ( ph /\ ps /\ ch ) -> th ) $.
    $( An inference based on modus ponens. $)
    mp3an1 $p |- ( ( ps /\ ch ) -> th ) $=
      ( wa 3expb mpan ) ABCGDEABCDFHI $.
      $( [21-Nov-1994] $)
  $}

  ${
    mp3an2.1 $e |- ps $.
    mp3an2.2 $e |- ( ( ph /\ ps /\ ch ) -> th ) $.
    $( An inference based on modus ponens. $)
    mp3an2 $p |- ( ( ph /\ ch ) -> th ) $=
      ( 3expa mpanl2 ) ABCDEABCDFGH $.
      $( [21-Nov-1994] $)
  $}

  ${
    mp3an3.1 $e |- ch $.
    mp3an3.2 $e |- ( ( ph /\ ps /\ ch ) -> th ) $.
    $( An inference based on modus ponens. $)
    mp3an3 $p |- ( ( ph /\ ps ) -> th ) $=
      ( wa 3expia mpi ) ABGCDEABCDFHI $.
      $( [21-Nov-1994] $)
  $}

  ${
    mp3an12.1 $e |- ph $.
    mp3an12.2 $e |- ps $.
    mp3an12.3 $e |- ( ( ph /\ ps /\ ch ) -> th ) $.
    $( An inference based on modus ponens. $)
    mp3an12 $p |- ( ch -> th ) $=
      ( mp3an1 mpan ) BCDFABCDEGHI $.
      $( [13-Jul-2005] $)
  $}

  ${
    mp3an13.1 $e |- ph $.
    mp3an13.2 $e |- ch $.
    mp3an13.3 $e |- ( ( ph /\ ps /\ ch ) -> th ) $.
    $( An inference based on modus ponens. $)
    mp3an13 $p |- ( ps -> th ) $=
      ( mp3an3 mpan ) ABDEABCDFGHI $.
      $( [14-Jul-2005] $)
  $}

  ${
    mp3an23.1 $e |- ps $.
    mp3an23.2 $e |- ch $.
    mp3an23.3 $e |- ( ( ph /\ ps /\ ch ) -> th ) $.
    $( An inference based on modus ponens. $)
    mp3an23 $p |- ( ph -> th ) $=
      ( mp3an3 mpan2 ) ABDEABCDFGHI $.
      $( [14-Jul-2005] $)
  $}

  ${
    mp3an1i.1 $e |- ps $.
    mp3an1i.2 $e |- ( ph -> ( ( ps /\ ch /\ th ) -> ta ) ) $.
    $( An inference based on modus ponens. $)
    mp3an1i $p |- ( ph -> ( ( ch /\ th ) -> ta ) ) $=
      ( wa wi w3a com12 mp3an1 ) CDHAEBCDAEIFABCDJEGKLK $.
      $( [5-Jul-2005] $)
  $}

  ${
    mp3anl1.1 $e |- ph $.
    mp3anl1.2 $e |- ( ( ( ph /\ ps /\ ch ) /\ th ) -> ta ) $.
    $( An inference based on modus ponens. $)
    mp3anl1 $p |- ( ( ( ps /\ ch ) /\ th ) -> ta ) $=
      ( wa wi w3a ex mp3an1 imp ) BCHDEABCDEIFABCJDEGKLM $.
      $( [24-Feb-2005] $)
  $}

  ${
    mp3anl2.1 $e |- ps $.
    mp3anl2.2 $e |- ( ( ( ph /\ ps /\ ch ) /\ th ) -> ta ) $.
    $( An inference based on modus ponens. $)
    mp3anl2 $p |- ( ( ( ph /\ ch ) /\ th ) -> ta ) $=
      ( wa wi w3a ex mp3an2 imp ) ACHDEABCDEIFABCJDEGKLM $.
      $( [24-Feb-2005] $)
  $}

  ${
    mp3anl3.1 $e |- ch $.
    mp3anl3.2 $e |- ( ( ( ph /\ ps /\ ch ) /\ th ) -> ta ) $.
    $( An inference based on modus ponens. $)
    mp3anl3 $p |- ( ( ( ph /\ ps ) /\ th ) -> ta ) $=
      ( wa wi w3a ex mp3an3 imp ) ABHDEABCDEIFABCJDEGKLM $.
      $( [24-Feb-2005] $)
  $}

  ${
    mp3anr1.1 $e |- ps $.
    mp3anr1.2 $e |- ( ( ph /\ ( ps /\ ch /\ th ) ) -> ta ) $.
    $( An inference based on modus ponens. $)
    mp3anr1 $p |- ( ( ph /\ ( ch /\ th ) ) -> ta ) $=
      ( wa w3a ancoms mp3anl1 ) CDHAEBCDAEFABCDIEGJKJ $.
      $( [4-Nov-2006] $)
  $}

  ${
    mp3anr2.1 $e |- ch $.
    mp3anr2.2 $e |- ( ( ph /\ ( ps /\ ch /\ th ) ) -> ta ) $.
    $( An inference based on modus ponens. $)
    mp3anr2 $p |- ( ( ph /\ ( ps /\ th ) ) -> ta ) $=
      ( wa w3a ancoms mp3anl2 ) BDHAEBCDAEFABCDIEGJKJ $.
      $( [24-Nov-2006] $)
  $}

  ${
    mp3anr3.1 $e |- th $.
    mp3anr3.2 $e |- ( ( ph /\ ( ps /\ ch /\ th ) ) -> ta ) $.
    $( An inference based on modus ponens. $)
    mp3anr3 $p |- ( ( ph /\ ( ps /\ ch ) ) -> ta ) $=
      ( wa w3a ancoms mp3anl3 ) BCHAEBCDAEFABCDIEGJKJ $.
      $( [19-Oct-2007] $)
  $}

  ${
    mp3an.1 $e |- ph $.
    mp3an.2 $e |- ps $.
    mp3an.3 $e |- ch $.
    mp3an.4 $e |- ( ( ph /\ ps /\ ch ) -> th ) $.
    $( An inference based on modus ponens. $)
    mp3an $p |- th $=
      ( mp3an1 mp2an ) BCDFGABCDEHIJ $.
      $( [14-May-1999] $)
  $}

  ${
    mpd3an3.2 $e |- ( ( ph /\ ps ) -> ch ) $.
    mpd3an3.3 $e |- ( ( ph /\ ps /\ ch ) -> th ) $.
    $( An inference based on modus ponens. $)
    mpd3an3 $p |- ( ( ph /\ ps ) -> th ) $=
      ( wa 3expa mpdan ) ABGCDEABCDFHI $.
      $( [8-Nov-2007] $)
  $}

  ${
    mpd3an23.1 $e |- ( ph -> ps ) $.
    mpd3an23.2 $e |- ( ph -> ch ) $.
    mpd3an23.3 $e |- ( ( ph /\ ps /\ ch ) -> th ) $.
    $( An inference based on modus ponens. $)
    mpd3an23 $p |- ( ph -> th ) $=
      ( id syl3anc ) AABCDAHEFGI $.
      $( [4-Dec-2006] $)
  $}

  ${
    biimp3a.1 $e |- ( ( ph /\ ps ) -> ( ch <-> th ) ) $.
    $( Infer implication from a logical equivalence.  Similar to ~ biimpa . $)
    biimp3a $p |- ( ( ph /\ ps /\ ch ) -> th ) $=
      ( wa biimpa 3impa ) ABCDABFCDEGH $.
      $( [4-Sep-2005] $)

    $( Infer implication from a logical equivalence.  Similar to ~ biimpar . $)
    biimp3ar $p |- ( ( ph /\ ps /\ th ) -> ch ) $=
      ( exbiri 3imp ) ABDCABCDEFG $.
      $( [2-Jan-2009] $)
  $}

  ${
    3anandis.1 $e |- ( ( ( ph /\ ps ) /\ ( ph /\ ch ) /\ ( ph /\ th ) )
                      -> ta ) $.
    $( Inference that undistributes a triple conjunction in the antecedent. $)
    3anandis $p |- ( ( ph /\ ( ps /\ ch /\ th ) ) -> ta ) $=
      ( w3a wa simpl simpr1 simpr2 simpr3 syl222anc ) ABCDGZHABACADEANIZABCDJOA
      BCDKOABCDLFM $.
      $( [18-Apr-2007] $)
  $}

  ${
    3anandirs.1 $e |- ( ( ( ph /\ th ) /\ ( ps /\ th ) /\ ( ch /\ th ) )
                      -> ta ) $.
    $( Inference that undistributes a triple conjunction in the antecedent. $)
    3anandirs $p |- ( ( ( ph /\ ps /\ ch ) /\ th ) -> ta ) $=
      ( w3a wa simpl1 simpr simpl2 simpl3 syl222anc ) ABCGZDHADBDCDEABCDINDJZAB
      CDKOABCDLOFM $.
      $( [18-Apr-2007] $) $( [25-Jul-2006] $)
  $}

  ${
    ecase23d.1 $e |- ( ph -> -. ch ) $.
    ecase23d.2 $e |- ( ph -> -. th ) $.
    ecase23d.3 $e |- ( ph -> ( ps \/ ch \/ th ) ) $.
    $( Deduction for elimination by cases. $)
    ecase23d $p |- ( ph -> ps ) $=
      ( wo wn ioran sylanbrc w3o 3orass sylib ord mt3d ) ABCDHZACIDIQIEFCDJKABQ
      ABCDLBQHGBCDMNOP $.
      $( [15-Jul-2005] $) $( [22-Apr-1994] $)
  $}

  ${
    3ecase.1 $e |- ( -. ph -> th ) $.
    3ecase.2 $e |- ( -. ps -> th ) $.
    3ecase.3 $e |- ( -. ch -> th ) $.
    3ecase.4 $e |- ( ( ph /\ ps /\ ch ) -> th ) $.
    $( Inference for elimination by cases. $)
    3ecase $p |- th $=
      ( wi 3exp wn a1d pm2.61i pm2.61nii ) BCDABCDIZIABCDHJAKZOBPDCELLMFGN $.
      $( [13-Jul-2005] $)
  $}

$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
      Other axiomatizations of classical propositional calculus
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
      Derive the Lukasiewicz axioms from Meredith's sole axiom
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Carew Meredith's sole axiom for propositional calculus.  This amazing
     formula is thought to be the shortest possible single axiom for
     propositional calculus with inference rule ~ ax-mp , where negation and
     implication are primitive.  Here we prove Meredith's axiom from ~ ax-1 ,
     ~ ax-2 , and ~ ax-3 .  Then from it we derive the Lukasiewicz axioms
     ~ luk-1 , ~ luk-2 , and ~ luk-3 .  Using these we finally re-derive our
     axioms as ~ ax1 , ~ ax2 , and ~ ax3 , thus proving the equivalence of all
     three systems.  C. A. Meredith, "Single Axioms for the Systems (C,N),
     (C,O) and (A,N) of the Two-Valued Propositional Calculus," _The Journal of
     Computing Systems_ vol. 1 (1953), pp. 155-164.  Meredith claimed to be
     close to a proof that this axiom is the shortest possible, but the proof
     was apparently never completed.

     An obscure Irish lecturer, Meredith (1904-1976) became enamored with logic
     somewhat late in life after attending talks by Lukasiewicz and produced
     many remarkable results such as this axiom.  From his obituary:  "He did
     logic whenever time and opportunity presented themselves, and he did it on
     whatever materials came to hand: in a pub, his favored pint of porter
     within reach, he would use the inside of cigarette packs to write proofs
     for logical colleagues."  (The proof was shortened by Andrew Salmon,
     25-Jul-2011.)  (The proof was shortened by Wolf Lammen, 28-May-2013.) $)
  meredith $p |- ( ( ( ( ( ph -> ps ) -> ( -. ch -> -. th ) ) -> ch ) ->
       ta ) -> ( ( ta -> ph ) -> ( th -> ph ) ) ) $=
    ( wi wn pm2.21 ax-3 imim12i com13 con1d com12 a1d ax-1 imim1d ja ) ABFZCGDG
    FZFZCFZEEAFZDAFZFUAGZUCUBDUDADAUATAGZDCUERSDCFABHCDIJKLMNEDEAEDOPQ $.
    $( [28-May-2013] $) $( [14-Dec-2002] $)

  $( Theorem ~ meredith restated as an axiom.  This will allow us to ensure
     that the rederivation of ~ ax1 , ~ ax2 , and ~ ax3 below depend only on
     Meredith's sole axiom and not accidentally on a previous theorem above.
     Outside of this section, we will not make use of this axiom. $)
  ax-meredith $a |- ( ( ( ( ( ph -> ps ) -> ( -. ch -> -. th ) ) -> ch ) ->
       ta ) -> ( ( ta -> ph ) -> ( th -> ph ) ) ) $.

  $( Step 3 of Meredith's proof of Lukasiewicz axioms from his sole axiom.
     (The step numbers refer to Meredith's original paper.) $)
  merlem1 $p |- ( ( ( ch -> ( -. ph -> ps ) ) -> ta ) -> ( ph -> ta ) ) $=
    ( wn wi ax-meredith ax-mp ) DAEZFIBFZEZIFFZJFCJFZFZMDFADFFJDECEFZEKEFZFOFDF
    LFNIBOKDGJPDCLGHDIJAMGH $.
    $( [14-Dec-2002] $)

  $( Step 4 of Meredith's proof of Lukasiewicz axioms from his sole axiom. $)
  merlem2 $p |- ( ( ( ph -> ph ) -> ch ) -> ( th -> ch ) ) $=
    ( wi wn merlem1 ax-meredith ax-mp ) BBDZAECEZDDADAADZDKBDCBDDAJIAFBBACKGH
    $.
    $( [14-Dec-2002] $)

  $( Step 7 of Meredith's proof of Lukasiewicz axioms from his sole axiom. $)
  merlem3 $p |- ( ( ( ps -> ch ) -> ph ) -> ( ch -> ph ) ) $=
    ( wi wn merlem2 ax-mp ax-meredith ) AADZCEZJDZDZCDBCDZDZMADCADZDOBEZPDDBDZL
    DZNKKDLDRJKIFKLQFGCABBLHGAACCMHG $.
    $( [14-Dec-2002] $)

  $( Step 8 of Meredith's proof of Lukasiewicz axioms from his sole axiom. $)
  merlem4 $p |- ( ta -> ( ( ta -> ph ) -> ( th -> ph ) ) ) $=
    ( wi wn ax-meredith merlem3 ax-mp ) AADBEZIDDBDZCDCADBADDZDCKDAABBCFKJCGH
    $.
    $( [14-Dec-2002] $)

  $( Step 11 of Meredith's proof of Lukasiewicz axioms from his sole axiom. $)
  merlem5 $p |- ( ( ph -> ps ) -> ( -. -. ph -> ps ) ) $=
    ( wi wn ax-meredith merlem1 merlem4 ax-mp ) BBCZBDZJCCBCBCIICCZABCZADZDZBCC
    ZBBBBBEIJNDCCBCZACZOCZKOCZBBBNAEOKDZCMTCCZACQCZRSCUAUBMBLTFAPUAGHOTAKQEHHH
    $.
    $( [14-Dec-2002] $)

  $( Step 12 of Meredith's proof of Lukasiewicz axioms from his sole axiom. $)
  merlem6 $p |- ( ch -> ( ( ( ps -> ch ) -> ph ) -> ( th -> ph ) ) ) $=
    ( wi merlem4 merlem3 ax-mp ) BCEZIAEDAEEZECJEADIFJBCGH $.
    $( [14-Dec-2002] $)

  $( Between steps 14 and 15 of Meredith's proof of Lukasiewicz axioms from his
     sole axiom. $)
  merlem7 $p |- ( ph -> ( ( ( ps -> ch ) -> th ) -> ( ( ( ch -> ta ) ->
                  ( -. th -> -. ps ) ) -> th ) ) ) $=
    ( wi wn merlem4 merlem6 ax-meredith ax-mp ) BCFZLDFZCEFDGBGFFZDFZFZFZAPFZDN
    LHPAGZFCGZSFFZCFLFZQRFOUAFUBSMOTICEDBUAJKPSCALJKK $.
    $( [22-Dec-2002] $)

  $( Step 15 of Meredith's proof of Lukasiewicz axioms from his sole axiom. $)
  merlem8 $p |- ( ( ( ps -> ch ) -> th ) -> ( ( ( ch -> ta ) ->
                  ( -. th -> -. ps ) ) -> th ) ) $=
    ( wph wi wn ax-meredith merlem7 ax-mp ) EEFZEGZLFFEFEFKKFFZABFCFBDFCGAGFFCF
    FEEEEEHMABCDIJ $.
    $( [22-Dec-2002] $)

  $( Step 18 of Meredith's proof of Lukasiewicz axioms from his sole axiom. $)
  merlem9 $p |- ( ( ( ph -> ps ) -> ( ch -> ( th -> ( ps -> ta ) ) ) ) ->
                    ( et -> ( ch -> ( th -> ( ps -> ta ) ) ) ) ) $=
    ( wi wn merlem6 merlem8 ax-mp ax-meredith ) CDBEGZGZGZFHZGBHZPGGZBGABGZGZSO
    GFOGGMRHDHGZHAHGZGUAGRGZTNRGUCPCNQIDMRUBJKBEUAARLKOPBFSLK $.
    $( [22-Dec-2002] $)

  $( Step 19 of Meredith's proof of Lukasiewicz axioms from his sole axiom. $)
  merlem10 $p |- ( ( ph -> ( ph -> ps ) ) -> ( th -> ( ph -> ps ) ) ) $=
    ( wi wn ax-meredith merlem9 ax-mp ) AADZAEZJDDADADIIDDZAABDZDZCLDDZAAAAAFLA
    DJCEDDADZADNDKNDLAACAFOAMCBKGHH $.
    $( [14-Dec-2002] $)

  $( Step 20 of Meredith's proof of Lukasiewicz axioms from his sole axiom. $)
  merlem11 $p |- ( ( ph -> ( ph -> ps ) ) -> ( ph -> ps ) ) $=
    ( wi wn ax-meredith merlem10 ax-mp ) AACZADZICCACACHHCCZAABCZCZKCZAAAAAELMC
    JMCABLFLKJFGG $.
    $( [14-Dec-2002] $)

  $( Step 28 of Meredith's proof of Lukasiewicz axioms from his sole axiom. $)
  merlem12 $p |- ( ( ( th -> ( -. -. ch -> ch ) ) -> ph ) -> ph ) $=
    ( wn wi merlem5 merlem2 ax-mp merlem4 merlem11 ) CBDDBEZEZAEZMAEZEZNLOBBEKE
    LBBFBKCGHAMLIHMAJH $.
    $( [14-Dec-2002] $)

  $( Step 35 of Meredith's proof of Lukasiewicz axioms from his sole axiom. $)
  merlem13 $p |- ( ( ph -> ps ) ->
              ( ( ( th -> ( -. -. ch -> ch ) ) -> -. -. ph ) -> ps ) ) $=
    ( wi wn merlem12 merlem5 ax-mp merlem6 ax-meredith merlem11 ) BBEZAFZDCFFCE
    EZNFZEZFZEZEAEZAEZABEQBEETUAEZUASUBOREZREZSRCDGRBEZRFPEZEREUCEZUDSEUFUGQPEU
    FPCDGQPHIRUEUFOJIRBRNUCKIIAMSTJITALIBBAQAKI $.
    $( [14-Dec-2002] $)

  $( 1 of 3 axioms for propositional calculus due to Lukasiewicz, derived from
     Meredith's sole axiom. $)
  luk-1 $p |- ( ( ph -> ps ) -> ( ( ps -> ch ) -> ( ph -> ch ) ) ) $=
    ( wi wn ax-meredith merlem13 ax-mp ) CCDZAEZEZEJDDKDBDZBCDACDDZDZABDZMDZCCK
    ABFMADZOEZEZERDDSDLDZNPDOLDTABJIGOLRQGHMASOLFHH $.
    $( [14-Dec-2002] $)

  $( 2 of 3 axioms for propositional calculus due to Lukasiewicz, derived from
     Meredith's sole axiom. $)
  luk-2 $p |- ( ( -. ph -> ph ) -> ph ) $=
    ( wn wi merlem5 merlem4 ax-mp merlem11 ax-meredith ) ABZACZJACZCZKAJBZCIBMC
    CZICZICZLOPCZPNQAMDIONEFOIGFAMIJIHFJAGF $.
    $( [14-Dec-2002] $)

  $( 3 of 3 axioms for propositional calculus due to Lukasiewicz, derived from
     Meredith's sole axiom. $)
  luk-3 $p |- ( ph -> ( -. ph -> ps ) ) $=
    ( wn wi merlem11 merlem1 ax-mp ) ACZHBDZDIDAIDHBEABHIFG $.
    $( [14-Dec-2002] $)

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
      Derive the standard axioms from the Lukasiewicz axioms
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    luklem1.1 $e |- ( ph -> ps ) $.
    luklem1.2 $e |- ( ps -> ch ) $.
    $( Used to rederive standard propositional axioms from Lukasiewicz'. $)
    luklem1 $p |- ( ph -> ch ) $=
      ( wi luk-1 ax-mp ) BCFZACFZEABFIJFDABCGHH $.
      $( [23-Dec-2002] $)
  $}

  $( Used to rederive standard propositional axioms from Lukasiewicz'. $)
  luklem2 $p |- ( ( ph -> -. ps ) ->
                ( ( ( ph -> ch ) -> th ) -> ( ps -> th ) ) ) $=
    ( wn wi luk-1 luk-3 ax-mp luklem1 ) ABEZFZBACFZFZMDFBDFFLKCFZMFZNAKCGBOFPNF
    BCHBOMGIJBMDGJ $.
    $( [22-Dec-2002] $)

  $( Used to rederive standard propositional axioms from Lukasiewicz'. $)
  luklem3 $p |- ( ph -> ( ( ( -. ph -> ps ) -> ch ) -> ( th -> ch ) ) ) $=
    ( wn wi luk-3 luklem2 luklem1 ) AAEZDEZFJBFCFDCFFAKGJDBCHI $.
    $( [22-Dec-2002] $)

  $( Used to rederive standard propositional axioms from Lukasiewicz'. $)
  luklem4 $p |- ( ( ( ( -. ph -> ph ) -> ph ) -> ps ) -> ps ) $=
    ( wn wi luk-2 luklem3 ax-mp luk-1 luklem1 ) ACADADZBDZBCZBDZBLJDZKMDJCJDJDZ
    NJEJONDAEJJJLFGGLJBHGBEI $.
    $( [22-Dec-2002] $)

  $( Used to rederive standard propositional axioms from Lukasiewicz'. $)
  luklem5 $p |- ( ph -> ( ps -> ph ) ) $=
    ( wn wi luklem3 luklem4 luklem1 ) AACADADBADZDHAAABEAHFG $.
    $( [22-Dec-2002] $)

  $( Used to rederive standard propositional axioms from Lukasiewicz'. $)
  luklem6 $p |- ( ( ph -> ( ph -> ps ) ) -> ( ph -> ps ) ) $=
    ( wi luk-1 wn luklem5 luklem2 luklem4 luklem1 ax-mp ) AABCZCKBCZKCZKAKBDKEZ
    KCZKCMKCZCZPMOCZQNLCRNBEZNCZLNSFTSBCBCLCLSKBBGBLHIINLKDJMOKDJKPHJI $.
    $( [22-Dec-2002] $)

  $( Used to rederive standard propositional axioms from Lukasiewicz'. $)
  luklem7 $p |- ( ( ph -> ( ps -> ch ) ) -> ( ps -> ( ph -> ch ) ) ) $=
    ( wi luk-1 luklem5 luklem1 luklem6 ax-mp ) ABCDZDJCDZACDZDZBLDZAJCEBKDMNDBJ
    KDZKBJBDOBJFJBCEGJCHGBKLEIG $.
    $( [22-Dec-2002] $)

  $( Used to rederive standard propositional axioms from Lukasiewicz'. $)
  luklem8 $p |- ( ( ph -> ps ) -> ( ( ch -> ph ) -> ( ch -> ps ) ) ) $=
    ( wi luk-1 luklem7 ax-mp ) CADZABDZCBDZDDIHJDDCABEHIJFG $.
    $( [22-Dec-2002] $)

  $( Standard propositional axiom derived from Lukasiewicz axioms. $)
  ax1 $p |- ( ph -> ( ps -> ph ) ) $=
    ( luklem5 ) ABC $.
    $( [22-Dec-2002] $)

  $( Standard propositional axiom derived from Lukasiewicz axioms. $)
  ax2 $p |- ( ( ph -> ( ps -> ch ) ) -> ( ( ph -> ps ) -> ( ph -> ch ) ) ) $=
    ( wi luklem7 luklem8 luklem6 ax-mp luklem1 ) ABCDDBACDZDZABDZJDZABCEKLAJDZD
    ZMBJAFNJDOMDACGNJLFHII $.
    $( [22-Dec-2002] $)

  $( Standard propositional axiom derived from Lukasiewicz axioms. $)
  ax3 $p |- ( ( -. ph -> -. ps ) -> ( ps -> ph ) ) $=
    ( wn wi luklem2 luklem4 luklem1 ) ACZBCDHADADBADZDIHBAAEAIFG $.
    $( [22-Dec-2002] $)

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Logical 'nand' (Sheffer stroke)
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $c -/\ $. $( 'nand' ) $)
  $( Extend wff definition to include 'nand'. $)
  wnand $a wff ( ph -/\ ps ) $.

  $( Define incompatibility ('not-and' or 'nand').  This is also called the
     Sheffer stroke, represented by a vertical bar, but we use a different
     symbol to avoid ambiguity with other uses of the vertical bar. $)
  df-nand $a |- ( ( ph -/\ ps ) <-> -. ( ph /\ ps ) ) $.

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
           Derive Nicod's axiom from the standard axioms
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Lemma for handling nested 'nand's. $)
  nic-justlem $p |- ( ( ph -/\ ( ch -/\ ps ) ) <-> ( ph -> ( ch /\ ps ) ) ) $=
    ( wnand wa wn wi df-nand anbi2i xchbinx iman bitr4i ) ACBDZDZACBEZFZEZFAOGN
    AMEQAMHMPACBHIJAOKL $.
    $( [11-Dec-2008] $) $( [19-Nov-2007] $)

  $( Show equivalence between implication and the Nicod version.  To derive
     ~ nic-dfim , apply ~ nic-justbi . $)
  nic-justim $p |- ( ( ph -> ps ) <-> ( ph -/\ ( ps -/\ ps ) ) ) $=
    ( wnand wa wi nic-justlem anidmdbi bitr2i ) ABBCCABBDEABEABBFABGH $.
    $( [17-Dec-2008] $) $( [19-Nov-2007] $)

  $( Show equivalence between negation and the Nicod version.  To derive
     ~ nic-dfneg , apply ~ nic-justbi . $)
  nic-justneg $p |- ( -. ps <-> ( ps -/\ ps ) ) $=
    ( wnand wn wa df-nand anidm xchbinx bicomi ) AABZACIAADAAAEAFGH $.
    $( [16-Dec-2008] $) $( [19-Nov-2007] $)

  $( Show equivalence between the bidirectional and the Nicod version.
     (Contributed by Jeff Hoffman, 19-Nov-2007.) $)
  nic-justbi $p |- ( ( ph <-> ps ) <->
          ( ( ph -/\ ps ) -/\ ( ( ph -/\ ph ) -/\ ( ps -/\ ps ) ) ) ) $=
    ( wa wn wo wnand pm4.57 df-nand nic-justneg anbi12i xchbinxr dfbi3 3bitr4ri
    wb xchbinx ) ABCZDZADZBDZCZDZCZDPTEABFZAAFZBBFZFZFZABNPTGUGUCUFCUBUCUFHUCQU
    FUAABHUFUDUECTUDUEHRUDSUEAIBIJKJOABLM $.
    $( [11-Dec-2008] $) $( [19-Nov-2007] $)

$( [suppress from the Table of Contents by breaking whitespace before "=-=-"]
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
           Prove Nicod's axiom and implication and negation definitions
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Define implication in terms of 'nand'.  Analogous to
     ` ( ( ph -/\ ( ps -/\ ps ) ) <-> ( ph -> ps ) ) ` .  In a pure
     (standalone) treatment of Nicod's axiom, this theorem would be changed to
     a definition ($a statement). $)
  nic-dfim $p |- ( ( ( ph -/\ ( ps -/\ ps ) ) -/\ ( ph -> ps ) ) -/\
                   ( ( ( ph -/\ ( ps -/\ ps ) ) -/\ ( ph -/\ ( ps -/\ ps ) ) )
                          -/\
                     ( ( ph -> ps ) -/\ ( ph -> ps ) ) ) ) $=
    ( wnand wi wb nic-justim bicomi nic-justbi mpbi ) ABBCCZABDZEJKCJJCKKCCCKJA
    BFGJKHI $.
    $( [11-Dec-2008] $)

  $( Define negation in terms of 'nand'.  Analogous to
     ` ( ( ph -/\ ph ) <-> -. ph ) ` .  In a pure (standalone) treatment of
     Nicod's axiom, this theorem would be changed to a definition ($a
     statement). $)
  nic-dfneg $p |- ( ( ( ph -/\ ph ) -/\ -. ph ) -/\
                    ( ( ( ph -/\ ph ) -/\ ( ph -/\ ph ) ) -/\
                      ( -. ph -/\ -. ph ) ) ) $=
    ( wnand wn wb nic-justneg bicomi nic-justbi mpbi ) AABZACZDIJBIIBJJBBBJIAEF
    IJGH $.
    $( [11-Dec-2008] $)

  ${
    $( Minor premise. $)
    nic-jmin $e |- ph $.
    $( Major premise. $)
    nic-jmaj $e |- ( ph -/\ ( ch -/\ ps ) ) $.
    $( Derive Nicod's rule of modus ponens using 'nand', from the standard
       one.  Although the major and minor premise together also imply ` ch ` ,
       this form is necessary for useful derivations from ~ nic-ax .  In a pure
       (standalone) treatment of Nicod's axiom, this theorem would be changed
       to an axiom ($a statement).  (Contributed by Jeff Hoffman,
       19-Nov-2007.) $)
    nic-mp $p |- ps $=
      ( wnand wa wi nic-justlem mpbi simprd ax-mp ) ABDACBACBFFACBGHEABCIJKL $.
      $( [11-Dec-2008] $) $( [19-Nov-2007] $)

    $( A direct proof of ~ nic-mp . $)
    nic-mpALT $p |- ps $=
      ( wa wi wn wnand df-nand anbi2i xchbinx mpbi iman mpbir simprd ax-mp ) AB
      DACBACBFZGARHZFZHZACBIZIZUAEUCAUBFTAUBJUBSACBJKLMARNOPQ $.
      $( [30-Dec-2008] $)
  $}

  $( Nicod's axiom derived from the standard ones.  See _Intro. to Math.
     Phil._ by B. Russell, p. 152.  Like ~ meredith , the usual axioms can be
     derived from this and vice versa.  Unlike ~ meredith , Nicod uses a
     different connective ('nand'), so another form of modus ponens must be
     used in proofs, e.g. ` { ` ~ nic-ax , ~ nic-mp ` } ` is equivalent to
     ` { ` ~ luk-1 , ~ luk-2 , ~ luk-3 , ~ ax-mp ` } ` .  In a pure
     (standalone) treatment of Nicod's axiom, this theorem would be changed to
     an axiom ($a statement).  (Contributed by Jeff Hoffman, 19-Nov-2007.) $)
  nic-ax $p |- ( ( ph -/\ ( ch -/\ ps ) ) -/\
                   ( ( ta -/\ ( ta -/\ ta ) ) -/\
                     ( ( th -/\ ch ) -/\
                       ( ( ph -/\ th ) -/\ ( ph -/\ th ) ) ) ) ) $=
    ( wnand wa wi nic-justlem biimpi simpl imim2i wn df-nand bitr4i con3 imim2d
    imnan con2b mpbir 3bitr4ri syl6ibr syl5bir nic-justim sylib pm4.24 jctil
    3syl ) ACBFFZEEEFFZDCFZADFZULFFZFFUIUJUMGHUIUMUJUIACBGZHZACHZUMUIUOABCIJUNC
    ACBKLUPUKULHUMUKDCMZHZUPULURDCGMUKDCRDCNOUPURDAMZHZULUPUQUSDACPQADMHADGMUTU
    LADRDASADNUAUBUCUKULUDUEUHUJEEEGZHEVAEUFJEEEITUGUIUMUJIT $.
    $( [11-Dec-2008] $) $( [19-Nov-2007] $)

  $( A direct proof of ~ nic-ax . $)
  nic-axALT $p |- ( ( ph -/\ ( ch -/\ ps ) ) -/\ ( ( ta -/\ ( ta -/\ ta ) )
          -/\ ( ( th -/\ ch ) -/\ ( ( ph -/\ th ) -/\ ( ph -/\ th ) ) ) ) ) $=
    ( wnand wa wn anidm df-nand anbi2i notbii iman 3bitr4i imnan bitr4i xchbinx
    wi anbi12i mpbir simpl imim2i con3 imim2d biimpri jctil con2b bitr3i 3bitri
    syl ) ACBFZFZEEEFZFZDCFZADFZUPFZFZFZFULUSGZHZVAACBGZRZEEEGZRZDCHZRZDAHZRZRZ
    GZRZVCVJVEVCACRZVJVBCACBUAUBVMVFVHDACUCUDUJVDEEIUEUFVAVCVKHZGZHVLUTVOULVCUS
    VNAUKGZHAVBHZGZHULVCVPVRUKVQACBJKLAUKJAVBMNUSUNURGVKUNURJUNVEURVJEUMGZHEVDH
    ZGZHUNVEVSWAUMVTEEEJKLEUMJEVDMNUOUQGZHVGVIHZGZHURVJWBWDUOVGUQWCUODCGHVGDCJD
    COPUQUPUPGZVIUPUPJWEUPADGHZVIUPIADJWFADHRVIADOADUGUHUIQSLUOUQJVGVIMNSQSLVCV
    KMPTULUSJT $.
    $( [11-Dec-2008] $)


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
          Derive the Lukasiewicz axioms from Nicod's axiom
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $( Minor premise. $)
    nic-imp.1 $e |- ( ph -/\ ( ch -/\ ps ) ) $.
    $( Inference for ~ nic-mp using ~ nic-ax as major premise.  (Contributed by
       Jeff Hoffman, 17-Nov-2007.) $)
    nic-imp $p |- ( ( th -/\ ch ) -/\ ( ( ph -/\ th ) -/\ ( ph -/\ th ) ) ) $=
      ( wta wnand nic-ax nic-mp ) ACBGGDCGADGZJGGFFFGGEABCDFHI $.
      $( [11-Dec-2008] $) $( [17-Nov-2007] $)
  $}

  $( Lemma for ~ nic-id . $)
  nic-idlem1 $p |- ( ( th -/\ ( ta -/\ ( ta -/\ ta ) ) ) -/\
                 ( ( ( ph -/\ ( ch -/\ ps ) ) -/\ th ) -/\
                   ( ( ph -/\ ( ch -/\ ps ) ) -/\ th ) ) ) $=
    ( wnand nic-ax nic-imp ) ACBFFACFAAFZIFFEEEFFDABCAEGH $.
    $( [11-Dec-2008] $) $( [17-Nov-2007] $)

  ${
    nic-idlem2.1 $e |- ( et -/\ ( ( ph -/\ ( ch -/\ ps ) ) -/\ th ) ) $.
    $( Lemma for ~ nic-id .  Inference used by ~ nic-id . $)
    nic-idlem2 $p |- ( ( th -/\ ( ta -/\ ( ta -/\ ta ) ) ) -/\ et ) $=
      ( wnand nic-ax nic-imp nic-mp ) FACBHHZDHZHDEEEHHZHZFHZPGOMMFLACHAAHZQHHN
      DABCAEIJJK $.
      $( [11-Dec-2008] $) $( [17-Nov-2007] $)
  $}

  $( Theorem ~ id expressed with ` -/\ ` .  (Contributed by Jeff Hoffman,
     17-Nov-2007.) $)
  nic-id $p |- ( ta -/\ ( ta -/\ ta ) ) $=
    ( wph wps wch wth wnand nic-ax nic-idlem2 nic-idlem1 nic-mp ) BCFZCBFZLFFZD
    DDFZFZFZCCCFFZFAAAFFZOEEEMDQCCCBEGHMNDPCORFKLLOAIHJ $.
    $( [11-Dec-2008] $) $( [17-Nov-2007] $)

  $( ` -/\ ` is symmetric.  (Contributed by Jeff Hoffman, 17-Nov-2007.) $)
  nic-swap $p |- ( ( th -/\ ph ) -/\ ( ( ph -/\ th ) -/\ ( ph -/\ th ) ) ) $=
    ( wta wnand nic-id nic-ax nic-mp ) AAADDBADABDZHDDCCCDDAEAAABCFG $.
    $( [11-Dec-2008] $) $( [17-Nov-2007] $)

  ${
    nic-isw1.1 $e |- ( th -/\ ph ) $.
    $( Inference version of ~ nic-swap .  (Contributed by Jeff Hoffman,
       17-Nov-2007.) $)
    nic-isw1 $p |- ( ph -/\ th ) $=
      ( wnand nic-swap nic-mp ) BADABDZGCABEF $.
      $( [11-Dec-2008] $) $( [17-Nov-2007] $)
  $}

  ${
    nic-isw2.1 $e |- ( ps -/\ ( th -/\ ph ) ) $.
    $( Inference for swapping nested terms.  (Contributed by Jeff Hoffman,
       17-Nov-2007.) $)
    nic-isw2 $p |- ( ps -/\ ( ph -/\ th ) ) $=
      ( wnand nic-swap nic-imp nic-mp nic-isw1 ) BACEZBCAEZEJBEZLDJKKBCAFGHI $.
      $( [11-Dec-2008] $) $( [17-Nov-2007] $)
  $}

  ${
    nic-iimp1.1 $e |- ( ph -/\ ( ch -/\ ps ) ) $.
    nic-iimp1.2 $e |- ( th -/\ ch ) $.
    $( Inference version of ~ nic-imp using right-handed term.  (Contributed by
       Jeff Hoffman, 17-Nov-2007.) $)
    nic-iimp1 $p |- ( th -/\ ph ) $=
      ( wnand nic-imp nic-mp nic-isw1 ) DADCGADGZKFABCDEHIJ $.
      $( [11-Dec-2008] $) $( [17-Nov-2007] $)
  $}

  ${
    nic-iimp2.1 $e |- ( ( ph -/\ ps ) -/\ ( ch -/\ ch ) ) $.
    nic-iimp2.2 $e |- ( th -/\ ph ) $.
    $( Inference version of ~ nic-imp using left-handed term.  (Contributed by
       Jeff Hoffman, 17-Nov-2007.) $)
    nic-iimp2 $p |- ( th -/\ ( ch -/\ ch ) ) $=
      ( wnand nic-isw1 nic-iimp1 ) CCGZBADJABGEHFI $.
      $( [11-Dec-2008] $) $( [17-Nov-2007] $)
  $}

  ${
    nic-idel.1 $e |- ( ph -/\ ( ch -/\ ps ) ) $.
    $( Inference to remove the trailing term.  (Contributed by Jeff Hoffman,
       17-Nov-2007.) $)
    nic-idel $p |- ( ph -/\ ( ch -/\ ch ) ) $=
      ( wnand nic-id nic-isw1 nic-imp nic-mp ) CCEZCEAJEZKJCCFGABCJDHI $.
      $( [11-Dec-2008] $) $( [17-Nov-2007] $)
  $}

  ${
    nic-ich.1 $e |- ( ph -/\ ( ps -/\ ps ) ) $.
    nic-ich.2 $e |- ( ps -/\ ( ch -/\ ch ) ) $.
    $( Chained inference.  (Contributed by Jeff Hoffman, 17-Nov-2007.) $)
    nic-ich $p |- ( ph -/\ ( ch -/\ ch ) ) $=
      ( wnand nic-isw1 nic-imp nic-mp ) CCFZBFAJFZKJBEGABBJDHI $.
      $( [11-Dec-2008] $) $( [17-Nov-2007] $)
  $}

  ${
    nic-idbl.1 $e |- ( ph -/\ ( ps -/\ ps ) ) $.
    $( Double the terms.  Since doubling is the same as negation, this can be
       viewed as a contraposition inference.  (Contributed by Jeff Hoffman,
       17-Nov-2007.) $)
    nic-idbl $p |- ( ( ps -/\ ps ) -/\ ( ( ph -/\ ph ) -/\ ( ph -/\ ph ) ) ) $=
      ( wnand nic-imp nic-ich ) BBDABDAADABBBCEABBACEF $.
      $( [11-Dec-2008] $) $( [17-Nov-2007] $)
  $}

$( (not in Table of Contents)
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Biconditional justification from Nicod's axiom
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( For nic-* definitions, the biconditional connective is not used.  Instead,
     definitions are made based on this form. ~ nic-bi1 and ~ nic-bi2 are used
     to convert the definitions into usable theorems about one side of the
     implication.  (Contributed by Jeff Hoffman, 18-Nov-2007.) $)
  nic-bijust $p |- ( ( ta -/\ ta ) -/\ ( ( ta -/\ ta ) -/\ ( ta -/\ ta ) ) ) $=
    ( nic-swap ) AAB $.
    $( [11-Dec-2008] $) $( [18-Nov-2007] $)

  ${
    $( 'Biconditional' premise.  (Contributed by Jeff Hoffman, 18-Nov-2007.) $)
    nic-bi1.1 $e |- ( ( ph -/\ ps ) -/\ ( ( ph -/\ ph )
         -/\ ( ps -/\ ps ) ) ) $.
    $( Inference to extract one side of an implication from a definition. $)
    nic-bi1 $p |- ( ph -/\ ( ps -/\ ps ) ) $=
      ( wnand nic-id nic-iimp1 nic-isw2 nic-idel ) AABBAAABDBBDAADACAEFGH $.
      $( [11-Dec-2008] $) $( [18-Nov-2007] $)
  $}

  ${
    $( 'Biconditional' premise.  (Contributed by Jeff Hoffman, 18-Nov-2007.) $)
    nic-bi2.1 $e |- ( ( ph -/\ ps ) -/\ ( ( ph -/\ ph )
         -/\ ( ps -/\ ps ) ) ) $.
    $( Inference to extract the other side of an implication from a
       'biconditional' definition. $)
    nic-bi2 $p |- ( ps -/\ ( ph -/\ ph ) ) $=
      ( wnand nic-isw2 nic-id nic-iimp1 nic-idel ) BBAABDZAADZBBDZBKIJCEBFGH $.
      $( [11-Dec-2008] $) $( [18-Nov-2007] $)
  $}

$( (not in Table of Contents)
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
             Prove the Lukasiewicz axioms from Nicod's axiom
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $( Minor premise. $)
    nic-smin $e |- ph $.
    $( Major premise. $)
    nic-smaj $e |- ( ph -> ps ) $.
    $( Derive the standard modus ponens from ~ nic-mp .  (Contributed by Jeff
       Hoffman, 18-Nov-2007.) $)
    nic-stdmp $p |- ps $=
      ( wi wnand nic-dfim nic-bi2 nic-mp ) ABBCABEZABBFFZKDKJABGHII $.
      $( [11-Dec-2008] $) $( [18-Nov-2007] $)
  $}

  $( Proof of ~ luk-1 from ~ nic-ax and ~ nic-mp (and definitions ~ nic-dfim
     and ~ nic-dfneg ).  Note that the standard axioms ~ ax-1 , ~ ax-2 , and
     ~ ax-3 are proved from the Lukasiewicz axioms by theorems ~ ax1 , ~ ax2 ,
     and ~ ax3 .  (Contributed by Jeff Hoffman, 18-Nov-2007.) $)
  nic-luk1 $p |- ( ( ph -> ps ) -> ( ( ps -> ch ) -> ( ph -> ch ) ) ) $=
    ( wta wi nic-dfim nic-bi2 nic-ax nic-isw2 nic-idel nic-bi1 nic-idbl nic-imp
    wnand nic-swap nic-ich nic-mp ) ABEZBCEZACEZEZUANNZRUAEZUCRABBNNZUAUDRABFGU
    DSTTNZNZUAUDCCNZBNZAUGNZUINZNZUFUDDDDNNZUKUKUDULABBUGDHIJUKUEUHNUFUEUJUJUHU
    ITUITACFKLMSUHUHUESBUGNZUHUMSBCFGUGBOPMPPUFUASTFKPPUBUCRUAFKQ $.
    $( [11-Dec-2008] $) $( [18-Nov-2007] $)

  $( Proof of ~ luk-2 from ~ nic-ax and ~ nic-mp .  (Contributed by Jeff
     Hoffman, 18-Nov-2007.) $)
  nic-luk2 $p |- ( ( -. ph -> ph ) -> ph ) $=
    ( wn wi wnand nic-dfim nic-bi2 nic-dfneg nic-id nic-iimp1 nic-isw2 nic-isw1
    nic-bi1 nic-mp ) ABZACZAADZDZOACZROPONPDZSPSONAEFNPPPNDNNDPPDPAGPHIJIKQROAE
    LM $.
    $( [11-Dec-2008] $) $( [18-Nov-2007] $)

  $( Proof of ~ luk-3 from ~ nic-ax and ~ nic-mp .  (Contributed by Jeff
     Hoffman, 18-Nov-2007.) $)
  nic-luk3 $p |- ( ph -> ( -. ph -> ps ) ) $=
    ( wn wi wnand nic-dfim nic-bi1 nic-dfneg nic-bi2 nic-id nic-iimp1 nic-iimp2
    nic-mp ) AACZBDZOEEZAODZQNBBEZOANREONBFGNAAEZSASNAHIAJKLPQAOFGM $.
    $( [11-Dec-2008] $) $( [18-Nov-2007] $)

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                True and false constants
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $c T. $.
  $c F. $.

  $( ` T. ` is a wff. $)
  wtru $a wff T. $.

  $( ` F. ` is a wff. $)
  wfal $a wff F. $.

  $( Soundness justification theorem for ~ df-tru . $)
  trujust $p |- ( ( ph <-> ph ) <-> ( ps <-> ps ) ) $=
    ( wb biid 2th ) AACBBCADBDE $.
    $( [17-Nov-2013] $)

  $( Definition of ` T. ` , a tautology. ` T. ` is a constant true.  In this
     definition ~ biid is used as an antecedent, however, any true wff, such as
     an axiom, can be used in its place. $)
  df-tru $a |- ( T. <-> ( ph <-> ph ) ) $.

  $( Definition of ` F. ` , a contradiction. ` F. ` is a constant false. $)
  df-fal $a |- ( F. <-> -. T. ) $.

  $( ` T. ` is provable.  (Contributed by Anthony Hart, 13-Oct-2010.) $)
  tru $p |- T. $=
    ( wph wtru wb biid df-tru mpbir ) BAACADAEF $.
    $( [6-Sep-2010] $) $( [13-Oct-2010] $)

  $( ` F. ` is not provable.  (Contributed by Anthony Hart, 22-Oct-2010.)  (The
     proof was shortened by Mel L. O'Cat, 11-Mar-2012.) $)
  notfal $p |- -. F. $=
    ( wfal wtru wn tru notnoti df-fal mtbir ) ABCBDEFG $.
    $( [11-Mar-2012] $) $( [22-Oct-2010] $)
  ${
    trud.1 $e |- ( T. -> ph ) $.
    $( Eliminate ` T. ` as an antecedent.  (Contributed by Mario Carneiro,
       13-Mar-2014.) $)
    trud $p |- ph $=
      ( wtru tru ax-mp ) CADBE $.
      $( [13-Mar-2014] $)
  $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
       Auxiliary theorems for Alan Sare's virtual deduction tool, part 1
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    ee22.1 $e |- ( ph -> ( ps -> ch ) ) $.
    ee22.2 $e |- ( ph -> ( ps -> th ) ) $.
    ee22.3 $e |- ( ch -> ( th -> ta ) ) $.
    $( Virtual deduction rule ~ e22 without virtual deduction connectives.
       Special theorem needed for Alan Sare's virtual deduction translation
       tool.  (Contributed by Alan Sare, 2-May-2011.) $)
    ee22 $p |- ( ph -> ( ps -> ta ) ) $=
      ( syl6c ) ABCDEFGHI $.
      $( [28-Oct-2011] $) $( [2-May-2011] $)
  $}

  ${
    ee12an.1 $e |- ( ph -> ps ) $.
    ee12an.2 $e |- ( ph -> ( ch -> th ) ) $.
    ee12an.3 $e |- ( ( ps /\ th ) -> ta ) $.
    $( ~ e12an without virtual deduction connectives.  Special theorem needed
       for Alan Sare's virtual deduction translation tool.  (Contributed by
       Alan Sare, 28-Oct-2011.) $)
    ee12an $p |- ( ph -> ( ch -> ta ) ) $=
      ( wa jctild syl6 ) ACBDIEACDBGFJHK $.
      $( [28-Oct-2011] $) $( [28-Oct-2011] $)
  $}

  ${
    ee23.1 $e |- ( ph -> ( ps -> ch ) ) $.
    ee23.2 $e |- ( ph -> ( ps -> ( th -> ta ) ) ) $.
    ee23.3 $e |- ( ch -> ( ta -> et ) ) $.
    $( ~ e23 without virtual deductions.  (Contributed by Alan Sare,
       17-Jul-2011.) $)
    ee23 $p |- ( ph -> ( ps -> ( th -> et ) ) ) $=
      ( wi syl6 syldd ) ABDEFHABCEFJGIKL $.
      $( [17-Jul-2011] $)
  $}

  $( Exportation implication also converting head from biconditional to
     conditional.  This proof is ~ exbirVD automatically translated and
     minimized.  (Contributed by Alan Sare, 31-Dec-2011.) $)
  exbir $p |- ( ( ( ph /\ ps ) -> ( ch <-> th ) ) ->
              ( ph -> ( ps -> ( th -> ch ) ) ) ) $=
    ( wa wb wi bi2 imim2i exp3a ) ABEZCDFZGABDCGZLMKCDHIJ $.
    $( [31-Dec-2011] $)

  $( ~ impexp with a 3-conjunct antecedent.  This proof is ~ 3impexpVD
     automatically translated and minimized.  (Contributed by Alan Sare,
     31-Dec-2011.) $)
  3impexp $p |- ( ( ( ph /\ ps /\ ch ) -> th ) <->
                ( ph -> ( ps -> ( ch -> th ) ) ) ) $=
    ( w3a wi id 3expd 3impd impbii ) ABCEDFZABCDFFFZKABCDKGHLABCDLGIJ $.
    $( [31-Dec-2011] $)

  $( ~ 3impexp with biconditional consequent of antecedent that is commuted in
     consequent.  Derived automatically from ~ 3impexpVD .  (Contributed by
     Alan Sare, 31-Dec-2011.) $)
  3impexpbicom $p |- ( ( ( ph /\ ps /\ ch ) -> ( th <-> ta ) ) <->
                     ( ph -> ( ps -> ( ch -> ( ta <-> th ) ) ) ) ) $=
    ( w3a wb wi bicom imbi2 biimpcd mpi 3expd 3impexp biimpri syl6ibr impbii )
    ABCFZDEGZHZABCEDGZHHHZTABCUATSUAGZRUAHZDEIZUCTUDSUARJKLMUBRUASUDUBABCUANOUE
    PQ $.
    $( [31-Dec-2011] $)

  ${
    3impexpbicomi.1 $e |- ( ( ph /\ ps /\ ch ) -> ( th <-> ta ) ) $.
    $( Deduction form of ~ 3impexpbicom .  Derived automatically from
       ~ 3impexpbicomiVD .  (Contributed by Alan Sare, 31-Dec-2011.) $)
    3impexpbicomi $p |- ( ph -> ( ps -> ( ch -> ( ta <-> th ) ) ) ) $=
      ( wb w3a bicomd 3exp ) ABCEDGABCHDEFIJ $.
      $( [31-Dec-2011] $)
  $}

  $( Closed form of ~ ancoms .  Derived automatically from ~ ancomsimpVD .
     (Contributed by Alan Sare, 31-Dec-2011.) $)
  ancomsimp $p |- ( ( ( ph /\ ps ) -> ch ) <-> ( ( ps /\ ph ) -> ch ) ) $=
    ( wa ancom imbi1i ) ABDBADCABEF $.
    $( [31-Dec-2011] $)

  ${
    exp3acom3r.1 $e |- ( ph -> ( ( ps /\ ch ) -> th ) ) $.
    $( Export and commute antecedents.  (Contributed by Alan Sare,
       18-Mar-2012.) $)
    exp3acom3r $p |- ( ps -> ( ch -> ( ph -> th ) ) ) $=
      ( exp3a com3l ) ABCDABCDEFG $.
      $( [18-Mar-2012] $)
  $}

  $( Implication form of ~ exp3acom23 .(Contributed by Alan Sare,
     22-Jul-2012.) $)
  exp3acom23g $p |- ( ( ph -> ( ( ps /\ ch ) -> th ) ) <->
                        ( ph -> ( ch -> ( ps -> th ) ) ) ) $=
    ( wa wi ancomsimp impexp bitri imbi2i ) BCEDFZCBDFFZAKCBEDFLBCDGCBDHIJ $.
    $( [22-Jul-2012] $)

  ${
    exp3acom23.1 $e |- ( ph -> ( ( ps /\ ch ) -> th ) ) $.
    $( The exportation deduction ~ exp3a with commutation of the conjoined
       wwfs.  (Contributed by Alan Sare, 22-Jul-2012.) $)
    exp3acom23 $p |- ( ph -> ( ch -> ( ps -> th ) ) ) $=
      ( exp3a com23 ) ABCDABCDEFG $.
      $( [22-Jul-2012] $)
  $}

  $( Implication form of ~ simplbi2com .  (Contributed by Alan Sare,
     22-Jul-2012.) $)
  simplbi2comg $p |- ( ( ph <-> ( ps /\ ch ) ) -> ( ch -> ( ps -> ph ) ) ) $=
    ( wa wb bi2 exp3acom23 ) ABCDZEBCAAHFG $.
    $( [22-Jul-2012] $)

  ${
    simplbi2com.1 $e |- ( ph <-> ( ps /\ ch ) ) $.
    $( A deduction eliminating a conjunct, similar to ~ simplbi2 .
       (Contributed by Alan Sare, 22-Jul-2012.)  (The proof was shortened by
       Wolf Lammen, 10-Nov-2012.) $)
    simplbi2com $p |- ( ch -> ( ps -> ph ) ) $=
      ( simplbi2 com12 ) BCAABCDEF $.
      $( [10-Nov-2012] $) $( [22-Jul-2012] $)
  $}

  ${
    $( Non-virtual deduction from of ~ e21 . ~ ee21 is ~ ee21VD without virtual
       deductions and was automatically derived from ~ ee21VD using the tools
       program translate..without..overwriting.cmd and Metamath's minimize
       command.  (Contributed by Alan Sare, 18-Mar-2012.)  $)

    ee21.1 $e |- ( ph -> ( ps -> ch ) ) $.
    ee21.2 $e |- ( ph -> th ) $.
    ee21.3 $e |- ( ch -> ( th -> ta ) ) $.
    $( ~ e21 without virtual deductions. $)
    ee21 $p |- ( ph -> ( ps -> ta ) ) $=
      ( a1d ee22 ) ABCDEFADBGIHJ $.
      $( [18-Mar-2012] $)
  $}

  ${
    ee10.1 $e |- ( ph -> ps ) $.
    ee10.2 $e |- ch $.
    ee10.3 $e |- ( ps -> ( ch -> th ) ) $.
    $( ~ e10 without virtual deductions. $)
    ee10 $p |- ( ph -> th ) $=
      ( mpi syl ) ABDEBCDFGHI $.
      $( [25-Jul-2011] $)
  $}

  ${
    ee02.1 $e |- ph $.
    ee02.2 $e |- ( ps -> ( ch -> th ) ) $.
    ee02.3 $e |- ( ph -> ( th -> ta ) ) $.
    $( ~ e02 without virtual deductions. $)
    ee02 $p |- ( ps -> ( ch -> ta ) ) $=
      ( a1i sylsyld ) BACDEABFIGHJ $.
      $( [22-Jul-2012] $)
  $}

$( End of auxiliary theorems for Alan Sare's virtual deduction tool, part 1 $)

$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
        Predicate calculus mostly without distinct variables
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  "Pure" (equality-free) predicate calculus axioms ax-5, ax-6, ax-7, ax-gen
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Declare new symbols needed for pure predicate calculus. $)
  $c A. $. $( "inverted A" universal quantifier (read:  "for all") $)
  $c set $. $( Individual variable type (read:  "the following is an
             individual (set) variable" $)

  $( Declare some names for individual variables. $)
  $v x $.
  $v y $.
  $v z $.
  $v w $.
  $v v $.
  $v u $.
  $( Let ` x ` be an individual variable. $)
  vx $f set x $.
  $( Let ` y ` be an individual variable. $)
  vy $f set y $.
  $( Let ` z ` be an individual variable. $)
  vz $f set z $.
  $( Let ` w ` be an individual variable. $)
  vw $f set w $.
  $( Let ` v ` be an individual variable. $)
  vv $f set v $.
  $( Let ` u ` be an individual variable. $)
  vu $f set u $.

  $( Extend wff definition to include the universal quantifier ('for all').
     ` A. x ph ` is read " ` ph ` (phi) is true for all ` x ` ."  Typically, in
     its final application ` ph ` would be replaced with a wff containing a
     (free) occurrence of the variable ` x ` , for example ` x = y ` .  In a
     universe with a finite number of objects, "for all" is equivalent to a big
     conjunction (AND) with one wff for each possible case of ` x ` .  When the
     universe is infinite (as with set theory), such a propositional-calculus
     equivalent is not possible because an infinitely long formula has no
     meaning, but conceptually the idea is the same. $)
  wal $a wff A. x ph $.

  $( Axiom of Quantified Implication.  Axiom C4 of [Monk2] p. 105. $)
  ax-5 $a |- ( A. x ( ph -> ps ) -> ( A. x ph -> A. x ps ) ) $.

  $( Axiom of Quantified Negation.  Axiom C5-2 of [Monk2] p. 113. $)
  ax-6 $a |- ( -. A. x ph -> A. x -. A. x ph ) $.

  $( Axiom of Quantifier Commutation.  This axiom says universal quantifiers
     can be swapped.  One of the 4 axioms of pure predicate calculus.  Axiom
     scheme C6' in [Megill] p. 448 (p. 16 of the preprint).  Also appears as
     Lemma 12 of [Monk2] p. 109 and Axiom C5-3 of [Monk2] p. 113.  An alternate
     axiomatization could use ~ ax467 in place of ~ ax-4 , ~ ax-6o , and
     ~ ax-7 . $)
  ax-7 $a |- ( A. x A. y ph -> A. y A. x ph ) $.

  ${
    ax-g.1 $e |- ph $.
    $( Rule of Generalization.  The postulated inference rule of pure predicate
       calculus.  See e.g.  Rule 2 of [Hamilton] p. 74.  This rule says that if
       something is unconditionally true, then it is true for all values of a
       variable.  For example, if we have proved ` x = x ` , we can conclude
       ` A. x x = x ` or even ` A. y x = x ` .  Theorem ~ a4i shows we can go
       the other way also: in other words we can add or remove universal
       quantifiers from the beginning of any theorem as required. $)
    ax-gen $a |- A. x ph $.
  $}

  $( Declare the existential quantifier symbol. $)
  $c E. $.   $( Backwards E (read:  "there exists") $)

  $( Extend wff definition to include the existential quantifier ("there
     exists"). $)
  wex $a wff E. x ph $.

  $( Define existential quantification. ` E. x ph ` means "there exists at
     least one set ` x ` such that ` ph ` is true."  Definition of [Margaris]
     p. 49. $)
  df-ex $a |- ( E. x ph <-> -. A. x -. ph ) $.

  ${
    gen2.1 $e |- ph $.
    $( Generalization applied twice. $)
    gen2 $p |- A. x A. y ph $=
      ( wal ax-gen ) ACEBACDFF $.
      $( [30-Apr-1998] $)
  $}

  ${
    mpg.1 $e |- ( A. x ph -> ps ) $.
    mpg.2 $e |- ph $.
    $( Modus ponens combined with generalization. $)
    mpg $p |- ps $=
      ( wal ax-gen ax-mp ) ACFBACEGDH $.
      $( [24-May-1994] $)
  $}

  ${
    mpgbi.1 $e |- ( A. x ph <-> ps ) $.
    mpgbi.2 $e |- ph $.
    $( Modus ponens on biconditional combined with generalization.  (The proof
       was shortened by Stefan Allan, 28-Oct-2008.) $)
    mpgbi $p |- ps $=
      ( wal ax-gen mpbi ) ACFBACEGDH $.
      $( [31-Oct-2008] $) $( [24-May-1994] $)
  $}

  ${
    mpgbir.1 $e |- ( ph <-> A. x ps ) $.
    mpgbir.2 $e |- ps $.
    $( Modus ponens on biconditional combined with generalization.  (The proof
       was shortened by Stefan Allan, 28-Oct-2008.) $)
    mpgbir $p |- ph $=
      ( wal ax-gen mpbir ) ABCFBCEGDH $.
      $( [31-Oct-2008] $) $( [24-May-1994] $)
  $}

  ${
    a7s.1 $e |- ( A. x A. y ph -> ps ) $.
    $( Swap quantifiers in an antecedent. $)
    a7s $p |- ( A. y A. x ph -> ps ) $=
      ( wal ax-7 syl ) ACFDFADFCFBADCGEH $.
      $( [5-Aug-1993] $)
  $}

  ${
    alimi.1 $e |- ( ph -> ps ) $.
    $( Inference quantifying both antecedent and consequent. $)
    alimi $p |- ( A. x ph -> A. x ps ) $=
      ( wi wal ax-5 mpg ) ABEACFBCFECABCGDH $.
      $( [5-Aug-1993] $)

    $( Inference doubly quantifying both antecedent and consequent. $)
    2alimi $p |- ( A. x A. y ph -> A. x A. y ps ) $=
      ( wal alimi ) ADFBDFCABDEGG $.
      $( [3-Feb-2005] $)
  $}

  $( Theorem 19.20 of [Margaris] p. 90.  (The proof was shortened by O'Cat,
     30-Mar-2008.) $)
  alim $p |- ( A. x ( ph -> ps ) -> ( A. x ph -> A. x ps ) ) $=
    ( ax-5 ) ABCD $.
    $( [30-Mar-2008] $) $( [5-Aug-1993] $)

  ${
    al2imi.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Inference quantifying antecedent, nested antecedent, and consequent. $)
    al2imi $p |- ( A. x ph -> ( A. x ps -> A. x ch ) ) $=
      ( wal wi alimi alim syl ) ADFBCGZDFBDFCDFGAKDEHBCDIJ $.
      $( [5-Aug-1993] $)
  $}

  ${
    alanimi.1 $e |- ( ( ph /\ ps ) -> ch ) $.
    $( Variant of ~ al2imi with conjunctive antecedent.  (Contributed by Andrew
       Salmon, 8-Jun-2011.) $)
    alanimi $p |- ( ( A. x ph /\ A. x ps ) -> A. x ch ) $=
      ( wal ex al2imi imp ) ADFBDFCDFABCDABCEGHI $.
      $( [8-Jun-2011] $)
  $}

  ${
    alimd.1 $e |- ( ph -> A. x ph ) $.
    alimd.2 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Deduction from Theorem 19.20 of [Margaris] p. 90. $)
    alimd $p |- ( ph -> ( A. x ps -> A. x ch ) ) $=
      ( wal wi al2imi syl ) AADGBDGCDGHEABCDFIJ $.
      $( [4-Jan-2002] $)
  $}

  $( Theorem 19.15 of [Margaris] p. 90. $)
  albi $p |- ( A. x ( ph <-> ps ) -> ( A. x ph <-> A. x ps ) ) $=
    ( wb wal bi1 al2imi bi2 impbid ) ABDZCEACEBCEJABCABFGJBACABHGI $.
    $( [5-Aug-1993] $)

  ${
    alrimi.1 $e |- ( ph -> A. x ph ) $.
    alrimi.2 $e |- ( ph -> ps ) $.
    $( Inference from Theorem 19.21 of [Margaris] p. 90. $)
    alrimi $p |- ( ph -> A. x ps ) $=
      ( wal alimi syl ) AACFBCFDABCEGH $.
      $( [5-Aug-1993] $)
  $}

  ${
    albii.1 $e |- ( ph <-> ps ) $.
    $( Inference adding universal quantifier to both sides of an
       equivalence. $)
    albii $p |- ( A. x ph <-> A. x ps ) $=
      ( wb wal albi mpg ) ABEACFBCFECABCGDH $.
      $( [7-Aug-1994] $)

    $( Inference adding 2 universal quantifiers to both sides of an
       equivalence. $)
    2albii $p |- ( A. x A. y ph <-> A. x A. y ps ) $=
      ( wal albii ) ADFBDFCABDEGG $.
      $( [9-Mar-1997] $)
  $}

  ${
    hbth.1 $e |- ph $.
    $( No variable is (effectively) free in a theorem.

       This and later "hypothesis-building" lemmas, with labels starting
       "hb...", allow us to construct proofs of formulas of the form
       ` |- ( ph -> A. x ph ) ` from smaller formulas of this form.  These are
       useful for constructing hypotheses that state " ` x ` is (effectively)
       not free in ` ph ` ." $)
    hbth $p |- ( ph -> A. x ph ) $=
      ( wal ax-gen a1i ) ABDAABCEF $.
      $( [5-Aug-1993] $)
  $}

  ${
    hbxfrbi.1 $e |- ( ph <-> ps ) $.
    hbxfrbi.2 $e |- ( ps -> A. x ps ) $.
    $( A utility lemma to transfer a bound-variable hypothesis builder into a
       definition.  See ~ hbxfreq for equality version.  (Contributed by
       Jonathan Ben-Naim, 3-Jun-2011.) $)
    hbxfrbi $p |- ( ph -> A. x ph ) $=
      ( wal albii 3imtr4i ) BBCFAACFEDABCDGH $.
      $( [3-Jun-2011] $)
  $}

  ${
    hbal.1 $e |- ( ph -> A. x ph ) $.
    $( If ` x ` is not free in ` ph ` , it is not free in ` A. y ph ` . $)
    hbal $p |- ( A. y ph -> A. x A. y ph ) $=
      ( wal alimi ax-7 syl ) ACEZABEZCEIBEAJCDFACBGH $.
      $( [5-Aug-1993] $)
  $}

  $( Theorem 19.5 of [Margaris] p. 89. $)
  alcom $p |- ( A. x A. y ph <-> A. y A. x ph ) $=
    ( wal ax-7 impbii ) ACDBDABDCDABCEACBEF $.
    $( [5-Aug-1993] $)

  $( Theorem 19.7 of [Margaris] p. 89. $)
  alnex $p |- ( A. x -. ph <-> -. E. x ph ) $=
    ( wex wn wal df-ex con2bii ) ABCADBEABFG $.
    $( [5-Aug-1993] $)

  $( Theorem 19.6 of [Margaris] p. 89. $)
  alex $p |- ( A. x ph <-> -. E. x -. ph ) $=
    ( wal wn wex notnot albii alnex bitri ) ABCADZDZBCJBEDAKBAFGJBHI $.
    $( [5-Aug-1993] $)

  $( Part of theorem *11.5 in [WhiteheadRussell] p. 164.  (Contributed by
     Andrew Salmon, 24-May-2011.) $)
  2nalexn $p |- ( -. A. x A. y ph <-> E. x E. y -. ph ) $=
    ( wn wex wal df-ex alex albii xchbinxr bicomi ) ADCEZBEZACFZBFZDMLDZBFOLBGN
    PBACHIJK $.
    $( [24-May-2011] $)

  $( Theorem 19.14 of [Margaris] p. 90. $)
  exnal $p |- ( E. x -. ph <-> -. A. x ph ) $=
    ( wal wn wex alex con2bii ) ABCADBEABFG $.
    $( [5-Aug-1993] $)

  $( Theorem 19.22 of [Margaris] p. 90.  (The proof was shortened by Wolf
     Lammen, 4-Jul-2014.) $)
  exim $p |- ( A. x ( ph -> ps ) -> ( E. x ph -> E. x ps ) ) $=
    ( wi wal wex wn con3 al2imi alnex 3imtr3g con4d ) ABDZCEZBCFZACFZNBGZCEAGZC
    EOGPGMQRCABHIBCJACJKL $.
    $( [4-Jul-2014] $) $( [5-Aug-1993] $)

  $( Obsolete proof of ~ exim as of 4-Jul-2014. $)
  eximOLD $p |- ( A. x ( ph -> ps ) -> ( E. x ph -> E. x ps ) ) $=
    ( wi wal wn wex con3 al2imi con3d df-ex 3imtr4g ) ABDZCEZAFZCEZFBFZCEZFACGB
    CGNRPMQOCABHIJACKBCKL $.
    $( [5-Aug-1993] $)

  ${
    eximi.1 $e |- ( ph -> ps ) $.
    $( Inference adding existential quantifier to antecedent and consequent. $)
    eximi $p |- ( E. x ph -> E. x ps ) $=
      ( wi wex exim mpg ) ABEACFBCFECABCGDH $.
      $( [5-Aug-1993] $)

    $( Inference adding 2 existential quantifiers to antecedent and
       consequent. $)
    2eximi $p |- ( E. x E. y ph -> E. x E. y ps ) $=
      ( wex eximi ) ADFBDFCABDEGG $.
      $( [3-Feb-2005] $)
  $}

  $( A transformation of quantifiers and logical connectives. $)
  alinexa $p |- ( A. x ( ph -> -. ps ) <-> -. E. x ( ph /\ ps ) ) $=
    ( wn wi wal wa wex imnan albii alnex bitri ) ABDEZCFABGZDZCFNCHDMOCABIJNCKL
    $.
    $( [19-Aug-1993] $)

  $( A relationship between two quantifiers and negation. $)
  alexn $p |- ( A. x E. y -. ph <-> -. E. x A. y ph ) $=
    ( wn wex wal exnal albii alnex bitri ) ADCEZBFACFZDZBFLBEDKMBACGHLBIJ $.
    $( [18-Aug-1993] $)

  $( Theorem *11.51 in [WhiteheadRussell] p. 164.  (Contributed by Andrew
     Salmon, 24-May-2011.)  (The proof was shortened by Wolf Lammen,
     25-Sep-2014.) $)
  2exnexn $p |- ( E. x A. y ph <-> -. A. x E. y -. ph ) $=
    ( wn wex wal alexn con2bii ) ADCEBFACFBEABCGH $.
    $( [25-Sep-2014] $) $( [24-May-2011] $)

  $( Obsolete proof of ~ 2exnexn as of 25-Sep-2014. $)
  2exnexnOLD $p |- ( E. x A. y ph <-> -. A. x E. y -. ph ) $=
    ( wal wex wn df-ex exnal albii notbii bitr4i ) ACDZBELFZBDZFAFCEZBDZFLBGPNO
    MBACHIJK $.
    $( [24-May-2011] $)


  $( Theorem 19.18 of [Margaris] p. 90. $)
  exbi $p |- ( A. x ( ph <-> ps ) -> ( E. x ph <-> E. x ps ) ) $=
    ( wb wal wex wi bi1 alimi exim syl bi2 impbid ) ABDZCEZACFZBCFZOABGZCEPQGNR
    CABHIABCJKOBAGZCEQPGNSCABLIBACJKM $.
    $( [5-Aug-1993] $)

  ${
    exbii.1 $e |- ( ph <-> ps ) $.
    $( Inference adding existential quantifier to both sides of an
       equivalence. $)
    exbii $p |- ( E. x ph <-> E. x ps ) $=
      ( wb wex exbi mpg ) ABEACFBCFECABCGDH $.
      $( [24-May-1994] $)
  $}

  ${
    2exbii.1 $e |- ( ph <-> ps ) $.
    $( Inference adding 2 existential quantifiers to both sides of an
       equivalence. $)
    2exbii $p |- ( E. x E. y ph <-> E. x E. y ps ) $=
      ( wex exbii ) ADFBDFCABDEGG $.
      $( [16-Mar-1995] $)
  $}

  ${
    3exbii.1 $e |- ( ph <-> ps ) $.
    $( Inference adding 3 existential quantifiers to both sides of an
       equivalence. $)
    3exbii $p |- ( E. x E. y E. z ph <-> E. x E. y E. z ps ) $=
      ( wex exbii 2exbii ) AEGBEGCDABEFHI $.
      $( [2-May-1995] $)
  $}

  $( A transformation of quantifiers and logical connectives.  (The proof was
     shortened by Wolf Lammen, 4-Sep-2014.) $)
  exanali $p |- ( E. x ( ph /\ -. ps ) <-> -. A. x ( ph -> ps ) ) $=
    ( wn wa wex wi wal annim exbii exnal bitri ) ABDEZCFABGZDZCFNCHDMOCABIJNCKL
    $.
    $( [4-Sep-2014] $) $( [25-Mar-1996] $)

  $( Obsolete proof of ~ exanali as of 4-Sep-2014. $)
  exanaliOLD $p |- ( E. x ( ph /\ -. ps ) <-> -. A. x ( ph -> ps ) ) $=
    ( wi wal wn wa wex iman albii alnex bitri con2bii ) ABDZCEZABFGZCHZOPFZCEQF
    NRCABIJPCKLM $.
    $( [25-Mar-1996] $)

  $( Commutation of conjunction inside an existential quantifier. $)
  exancom $p |- ( E. x ( ph /\ ps ) <-> E. x ( ps /\ ph ) ) $=
    ( wa ancom exbii ) ABDBADCABEF $.
    $( [18-Aug-1993] $)

  ${
    alrimd.1 $e |- ( ph -> A. x ph ) $.
    alrimd.2 $e |- ( ps -> A. x ps ) $.
    alrimd.3 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Deduction from Theorem 19.21 of [Margaris] p. 90.  (The proof was
       shortened by Andrew Salmon, 13-May-2011.) $)
    alrimd $p |- ( ph -> ( ps -> A. x ch ) ) $=
      ( wal alimd syl5 ) BBDHACDHFABCDEGIJ $.
      $( [16-May-2011] $) $( [10-Feb-1997] $)
  $}

  ${
    eximd.1 $e |- ( ph -> A. x ph ) $.
    eximd.2 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Deduction from Theorem 19.22 of [Margaris] p. 90. $)
    eximd $p |- ( ph -> ( E. x ps -> E. x ch ) ) $=
      ( wi wal wex alrimi exim syl ) ABCGZDHBDICDIGAMDEFJBCDKL $.
      $( [20-May-1996] $)
  $}

  ${
    nex.1 $e |- -. ph $.
    $( Generalization rule for negated wff. $)
    nex $p |- -. E. x ph $=
      ( wn wex alnex mpgbi ) ADABEDBABFCG $.
      $( [18-May-1994] $)
  $}

  ${
    nexd.1 $e |- ( ph -> A. x ph ) $.
    nexd.2 $e |- ( ph -> -. ps ) $.
    $( Deduction for generalization rule for negated wff. $)
    nexd $p |- ( ph -> -. E. x ps ) $=
      ( wn wal wex alrimi alnex sylib ) ABFZCGBCHFALCDEIBCJK $.
      $( [2-Jan-2002] $)
  $}

  ${
    albid.1 $e |- ( ph -> A. x ph ) $.
    albid.2 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Formula-building rule for universal quantifier (deduction rule). $)
    albid $p |- ( ph -> ( A. x ps <-> A. x ch ) ) $=
      ( wb wal alrimi albi syl ) ABCGZDHBDHCDHGALDEFIBCDJK $.
      $( [5-Aug-1993] $)
  $}

  ${
    exbid.1 $e |- ( ph -> A. x ph ) $.
    exbid.2 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Formula-building rule for existential quantifier (deduction rule). $)
    exbid $p |- ( ph -> ( E. x ps <-> E. x ch ) ) $=
      ( wb wal wex alrimi exbi syl ) ABCGZDHBDICDIGAMDEFJBCDKL $.
      $( [5-Aug-1993] $)
  $}

  $( Simplification of an existentially quantified conjunction.  (Contributed
     by Rodolfo Medina, 25-Sep-2010.)  (The proof was shortened by Andrew
     Salmon, 29-Jun-2011.) $)
  exsimpl $p |- ( E. x ( ph /\ ps ) -> E. x ph ) $=
    ( wa simpl eximi ) ABDACABEF $.
    $( [29-Jun-2011] $) $( [25-Sep-2010] $)

  $( Theorem 19.26 of [Margaris] p. 90.  Also Theorem *10.22 of
     [WhiteheadRussell] p. 119.  (The proof was shortened by Wolf Lammen,
     4-Jul-2014.) $)
  19.26 $p |- ( A. x ( ph /\ ps ) <-> ( A. x ph /\ A. x ps ) ) $=
    ( wa wal simpl alimi simpr jca id alanimi impbii ) ABDZCEZACEZBCEZDNOPMACAB
    FGMBCABHGIABMCMJKL $.
    $( [4-Jul-2014] $) $( [5-Aug-1993] $)

  $( Obsolete proof of ~ 19.26 as of 4-Jul-2014. $)
  19.26OLD $p |- ( A. x ( ph /\ ps ) <-> ( A. x ph /\ A. x ps ) ) $=
    ( wa wal simpl alimi simpr jca pm3.2 al2imi imp impbii ) ABDZCEZACEZBCEZDOP
    QNACABFGNBCABHGIPQOABNCABJKLM $.
    $( [5-Aug-1993] $)

  $( Theorem 19.26 of [Margaris] p. 90 with two quantifiers. $)
  19.26-2 $p |- ( A. x A. y ( ph /\ ps ) <->
                ( A. x A. y ph /\ A. x A. y ps ) ) $=
    ( wa wal 19.26 albii bitri ) ABEDFZCFADFZBDFZEZCFKCFLCFEJMCABDGHKLCGI $.
    $( [3-Feb-2005] $)

  $( Theorem 19.26 of [Margaris] p. 90 with triple conjunction. $)
  19.26-3an $p |- ( A. x ( ph /\ ps /\ ch )
                   <-> ( A. x ph /\ A. x ps /\ A. x ch ) ) $=
    ( wa wal w3a 19.26 anbi1i bitri df-3an albii 3bitr4i ) ABEZCEZDFZADFZBDFZEZ
    CDFZEZABCGZDFQRTGPNDFZTEUANCDHUCSTABDHIJUBODABCKLQRTKM $.
    $( [13-Sep-2011] $)

  $( Theorem 19.29 of [Margaris] p. 90.  (The proof was shortened by Andrew
     Salmon, 13-May-2011.) $)
  19.29 $p |- ( ( A. x ph /\ E. x ps ) -> E. x ( ph /\ ps ) ) $=
    ( wal wex wa wi pm3.2 alimi exim syl imp ) ACDZBCEZABFZCEZMBOGZCDNPGAQCABHI
    BOCJKL $.
    $( [16-May-2011] $) $( [5-Aug-1993] $)

  $( Variation of Theorem 19.29 of [Margaris] p. 90. $)
  19.29r $p |- ( ( E. x ph /\ A. x ps ) -> E. x ( ph /\ ps ) ) $=
    ( wal wex wa 19.29 ancom exancom 3imtr4i ) BCDZACEZFBAFCELKFABFCEBACGLKHABC
    IJ $.
    $( [18-Aug-1993] $)

  $( Variation of Theorem 19.29 of [Margaris] p. 90 with double
     quantification. $)
  19.29r2 $p |- ( ( E. x E. y ph /\ A. x A. y ps ) ->
             E. x E. y ( ph /\ ps ) ) $=
    ( wex wal wa 19.29r eximi syl ) ADEZCEBDFZCFGKLGZCEABGDEZCEKLCHMNCABDHIJ $.
    $( [3-Feb-2005] $)

  $( Variation of Theorem 19.29 of [Margaris] p. 90 with mixed
     quantification. $)
  19.29x $p |- ( ( E. x A. y ph /\ A. x E. y ps ) ->
             E. x E. y ( ph /\ ps ) ) $=
    ( wal wex wa 19.29r 19.29 eximi syl ) ADEZCFBDFZCEGLMGZCFABGDFZCFLMCHNOCABD
    IJK $.
    $( [11-Feb-2005] $)

  $( Theorem 19.35 of [Margaris] p. 90.  This theorem is useful for moving an
     implication (in the form of the right-hand side) into the scope of a
     single existential quantifier.  (The proof was shortened by Wolf Lammen,
     27-Jun-2014.) $)
  19.35 $p |- ( E. x ( ph -> ps ) <-> ( A. x ph -> E. x ps ) ) $=
    ( wi wex wal wn wa 19.26 annim albii alnex anbi2i 3bitr3i con4bii ) ABDZCEZ
    ACFZBCEZDZPGZCFZRSGZHZQGTGABGZHZCFRUECFZHUBUDAUECIUFUACABJKUGUCRBCLMNPCLRSJ
    NO $.
    $( [27-Jun-2014] $) $( [5-Aug-1993] $)

  $( Obsolete proof of ~ 19.35 as of 27-Jun-2014. $)
  19.35OLD $p |- ( E. x ( ph -> ps ) <-> ( A. x ph -> E. x ps ) ) $=
    ( wal wn wi wex wa 19.26 annim albii df-an 3bitr3i con2bii imbi2i 3bitr4ri
    df-ex ) ACDZBEZCDZEZFZABFZEZCDZERBCGZFUCCGUEUBASHZCDRTHUEUBEASCIUGUDCABJKRT
    LMNUFUARBCQOUCCQP $.
    $( [5-Aug-1993] $)

  ${
    19.35i.1 $e |- E. x ( ph -> ps ) $.
    $( Inference from Theorem 19.35 of [Margaris] p. 90. $)
    19.35i $p |- ( A. x ph -> E. x ps ) $=
      ( wi wex wal 19.35 mpbi ) ABECFACGBCFEDABCHI $.
      $( [5-Aug-1993] $)
  $}

  ${
    19.35ri.1 $e |- ( A. x ph -> E. x ps ) $.
    $( Inference from Theorem 19.35 of [Margaris] p. 90. $)
    19.35ri $p |- E. x ( ph -> ps ) $=
      ( wi wex wal 19.35 mpbir ) ABECFACGBCFEDABCHI $.
      $( [5-Aug-1993] $)
  $}

  $( Theorem 19.25 of [Margaris] p. 90. $)
  19.25 $p |- ( A. y E. x ( ph -> ps ) ->
              ( E. y A. x ph -> E. y E. x ps ) ) $=
    ( wi wex wal 19.35 biimpi alimi exim syl ) ABECFZDGACGZBCFZEZDGNDFODFEMPDMP
    ABCHIJNODKL $.
    $( [5-Aug-1993] $)

  $( Theorem 19.30 of [Margaris] p. 90.  (The proof was shortened by Andrew
     Salmon, 25-May-2011.) $)
  19.30 $p |- ( A. x ( ph \/ ps ) -> ( A. x ph \/ E. x ps ) ) $=
    ( wn wi wal wex wo exnal exim syl5bir df-or albii 3imtr4i ) ADZBEZCFZACFZDZ
    BCGZEABHZCFRTHSOCGQTACIOBCJKUAPCABLMRTLN $.
    $( [25-May-2011] $) $( [5-Aug-1993] $)

  $( Theorem 19.43 of [Margaris] p. 90.  (The proof was shortened by Wolf
     Lammen, 27-Jun-2014.) $)
  19.43 $p |- ( E. x ( ph \/ ps ) <-> ( E. x ph \/ E. x ps ) ) $=
    ( wo wex wn wi wal df-or exbii 19.35 alnex imbi1i 3bitri bitr4i ) ABDZCEZAC
    EZFZBCEZGZRTDQAFZBGZCEUBCHZTGUAPUCCABIJUBBCKUDSTACLMNRTIO $.
    $( [27-Jun-2014] $) $( [5-Aug-1993] $)

  $( Obsolete proof of ~ 19.43 as of 27-Jun-2014. $)
  19.43OLD $p |- ( E. x ( ph \/ ps ) <-> ( E. x ph \/ E. x ps ) ) $=
    ( wo wn wal wex wa ioran albii 19.26 alnex anbi12i 3bitri notbii df-ex oran
    3bitr4i ) ABDZEZCFZEACGZEZBCGZEZHZESCGUBUDDUAUFUAAEZBEZHZCFUGCFZUHCFZHUFTUI
    CABIJUGUHCKUJUCUKUEACLBCLMNOSCPUBUDQR $.
    $( [5-Aug-1993] $)

  $( Theorem 19.33 of [Margaris] p. 90. $)
  19.33 $p |- ( ( A. x ph \/ A. x ps ) -> A. x ( ph \/ ps ) ) $=
    ( wal wo orc alimi olc jaoi ) ACDABEZCDBCDAJCABFGBJCBAHGI $.
    $( [5-Aug-1993] $)

  $( The antecedent provides a condition implying the converse of ~ 19.33 .
     Compare Theorem 19.33 of [Margaris] p. 90.  (The proof was shortened by
     Andrew Salmon, 25-May-2011.)  (The proof was shortened by Wolf Lammen,
     5-Jul-2014.) $)
  19.33b $p |- ( -. ( E. x ph /\ E. x ps ) ->
               ( A. x ( ph \/ ps ) <-> ( A. x ph \/ A. x ps ) ) ) $=
    ( wex wa wn wo wal ianor alnex pm2.53 al2imi syl5bir olc syl6com orcomd ord
    wi 19.30 orc jaoi sylbi 19.33 impbid1 ) ACDZBCDZEFZABGZCHZACHZBCHZGZUGUEFZU
    FFZGUIULRZUEUFIUMUOUNUIUMUKULUMAFZCHUIUKACJUHUPBCABKLMUKUJNOUIUNUJULUIUFUJU
    IUJUFABCSPQUJUKTOUAUBABCUCUD $.
    $( [5-Jul-2014] $) $( [27-Mar-2004] $)

  $( Obsolete proof of ~ 19.33b as of 22-Mar-2014. $)
  19.33bOLD $p |- ( -. ( E. x ph /\ E. x ps ) ->
               ( A. x ( ph \/ ps ) <-> ( A. x ph \/ A. x ps ) ) ) $=
    ( wex wa wn wo wal wi ianor alnex wb biorf alimi albi syl olc syl6bir 19.30
    sylbir orc a1i pm2.21 jaod syl5 jaoi sylbi 19.33 impbid1 ) ACDZBCDZEFZABGZC
    HZACHZBCHZGZULUJFZUKFZGUNUQIZUJUKJURUTUSURAFZCHZUTACKVBUNUPUQVBBUMLZCHUPUNL
    VAVCCABMNBUMCOPUPUOQRTUNUOUKGUSUQABCSUSUOUQUKUOUQIUSUOUPUAUBUKUQUCUDUEUFUGA
    BCUHUI $.
    $( [25-May-2011] $) $( [27-Mar-2004] $)

  $( Theorem 19.40 of [Margaris] p. 90. $)
  19.40 $p |- ( E. x ( ph /\ ps ) -> ( E. x ph /\ E. x ps ) ) $=
    ( wa wex exsimpl simpr eximi jca ) ABDZCEACEBCEABCFJBCABGHI $.
    $( [5-Aug-1993] $)

  $( Theorem *11.42 in [WhiteheadRussell] p. 163.  Theorem 19.40 of [Margaris]
     p. 90 with 2 quantifiers.  (Contributed by Andrew Salmon, 24-May-2011.) $)
  19.40-2 $p |- ( E. x E. y ( ph /\ ps ) ->
        ( E. x E. y ph /\ E. x E. y ps ) ) $=
    ( wa wex 19.40 eximi syl ) ABEDFZCFADFZBDFZEZCFKCFLCFEJMCABDGHKLCGI $.
    $( [24-May-2011] $)

  $( Theorem *11.21 in [WhiteheadRussell] p. 160.  (Contributed by Andrew
     Salmon, 24-May-2011.) $)
  alrot3 $p |- ( A. x A. y A. z ph <-> A. y A. z A. x ph ) $=
    ( wal alcom albii bitri ) ADEZCEBEIBEZCEABEDEZCEIBCFJKCABDFGH $.
    $( [24-May-2011] $)

  $( Rotate 4 universal quantifiers twice.  (The proof was shortened by Wolf
     Lammen, 28-Jun-2014.) $)
  alrot4 $p |- ( A. x A. y A. z A. w ph <-> A. z A. w A. x A. y ph ) $=
    ( wal alrot3 albii alcom 3bitri ) AEFDFCFZBFACFZEFZDFZBFMBFZDFLBFEFZDFKNBAC
    DEGHMBDIOPDLBEIHJ $.
    $( [28-Jun-2014] $) $( [2-Feb-2005] $)

  $( Obsolete proof of ~ alrot4 as of 28-Jun-2014. $)
  alrot4OLD $p |- ( A. x A. y A. z A. w ph <-> A. z A. w A. x A. y ph ) $=
    ( wal alcom albii bitri 3bitri ) AEFZDFCFZBFACFZEFZDFZBFNBFZDFMBFEFZDFLOBLK
    CFZDFOKCDGRNDACEGHIHNBDGPQDMBEGHJ $.
    $( [2-Feb-2005] $)

  $( Split a biconditional and distribute quantifier. $)
  albiim $p |- ( A. x ( ph <-> ps ) <->
             ( A. x ( ph -> ps ) /\ A. x ( ps -> ph ) ) ) $=
    ( wb wal wi wa dfbi2 albii 19.26 bitri ) ABDZCEABFZBAFZGZCEMCENCEGLOCABHIMN
    CJK $.
    $( [18-Aug-1993] $)

  $( Split a biconditional and distribute 2 quantifiers. $)
  2albiim $p |- ( A. x A. y ( ph <-> ps ) <->
             ( A. x A. y ( ph -> ps ) /\ A. x A. y ( ps -> ph ) ) ) $=
    ( wb wal wi wa albiim albii 19.26 bitri ) ABEDFZCFABGDFZBAGDFZHZCFNCFOCFHMP
    CABDIJNOCKL $.
    $( [3-Feb-2005] $)

  ${
    hband.1 $e |- ( ph -> ( ps -> A. x ps ) ) $.
    hband.2 $e |- ( ph -> ( ch -> A. x ch ) ) $.
    $( Deduction form of bound-variable hypothesis builder ~ hban . $)
    hband $p |- ( ph -> ( ( ps /\ ch ) -> A. x ( ps /\ ch ) ) ) $=
      ( wa wal anim12d 19.26 syl6ibr ) ABCGZBDHZCDHZGLDHABMCNEFIBCDJK $.
      $( [2-Jan-2002] $)
  $}

  ${
    hb3and.1 $e |- ( ph -> ( ps -> A. x ps ) ) $.
    hb3and.2 $e |- ( ph -> ( ch -> A. x ch ) ) $.
    hb3and.3 $e |- ( ph -> ( th -> A. x th ) ) $.
    $( Deduction form of bound-variable hypothesis builder ~ hb3an . $)
    hb3and $p |- ( ph -> ( ( ps /\ ch /\ th ) -> A. x ( ps /\ ch /\ th ) ) ) $=
      ( w3a wal 3anim123d 19.26-3an syl6ibr ) ABCDIZBEJZCEJZDEJZINEJABOCPDQFGHK
      BCDELM $.
      $( [17-Feb-2013] $)
  $}

  ${
    hbald.1 $e |- ( ph -> A. y ph ) $.
    hbald.2 $e |- ( ph -> ( ps -> A. x ps ) ) $.
    $( Deduction form of bound-variable hypothesis builder ~ hbal . $)
    hbald $p |- ( ph -> ( A. y ps -> A. x A. y ps ) ) $=
      ( wal alimd ax-7 syl6 ) ABDGZBCGZDGKCGABLDEFHBDCIJ $.
      $( [2-Jan-2002] $)
  $}

  $( Add/remove a conjunct in the scope of an existential quantifier.
     (Contributed by Raph Levien, 3-Jul-2006.) $)
  exintrbi $p |- ( A. x ( ph -> ps ) -> ( E. x ph <-> E. x ( ph /\ ps ) ) ) $=
    ( wi wal wa wb wex pm4.71 albii exbi sylbi ) ABDZCEAABFZGZCEACHNCHGMOCABIJA
    NCKL $.
    $( [3-Jul-2006] $)

  $( Introduce a conjunct in the scope of an existential quantifier. $)
  exintr $p |- ( A. x ( ph -> ps ) -> ( E. x ph -> E. x ( ph /\ ps ) ) ) $=
    ( wi wal wex wa exintrbi biimpd ) ABDCEACFABGCFABCHI $.
    $( [11-Aug-1993] $)

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
    Introduce equality axioms ax-8 through ax-14 except ax-9
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( --- Start of patch to prevent connective overloading $)
  $c exp $.
  $( This syntax construction states that a variable ` x ` , which has been
     declared to be a set variable by $f statement vx, is also a class
     expression.  This can be justified informally as follows.  We know that
     the exp builder ` { y | y e. x } ` is a exp by ~ cab .  Since (when ` y `
     is distinct from ` x ` ) we have ` x = { y | y e. x } ` by ~ cvjust , we
     can argue that that the syntax " ` exp x ` " can be viewed as an
     abbreviation for " ` exp { y | y e. x } ` ".  See the discussion under the
     definition of exp in [Jech] p. 4 showing that "Every set can be considered
     to be a class."

     While it is tempting and perhaps occasionally useful to view ~ cv as a
     "type conversion" from a set variable to a exp variable, keep in mind that
     ~ cv is intrinsically no different from any other class-building syntax
     such as ~ cab , ~ cun , or ~ c0 .

     (The description above applies to set theory, not predicate calculus.  The
     purpose of introducing ` exp x ` here, and not in set theory where it
     belongs, is to allow us to express i.e.  "prove" the ~ weq of predicate
     calculus from the ~ wceq of set theory, so that we don't "overload" the
     ` = ` connective with two syntax definitions.  This is done to prevent
     ambiguity that would complicate some Metamath parsers.) $)
  cv $a exp x $.
  $( --- End of patch to prevent connective overloading $)

  $( --- Start of old code before overloading prevention patch. $)
  $(          (None - the above patch had no old code.) $)
  $( --- End of old code before overloading prevention patch. $)

  $( Declare the equality predicate symbol. $)
  $c = $.  $( Equal sign (read:  'is equal to') $)

  $( --- Start of patch to prevent connective overloading $)
  ${
    $v A $.
    $v B $.
    wceq.cA $f exp A $.
    wceq.cB $f exp B $.
    $( Extend wff definition to include exp equality.

       (The purpose of introducing ` wff A = B ` here, and not in set theory
       where it belongs, is to allow us to express i.e.  "prove" the ~ weq of
       predicate calculus in terms of the ~ wceq of set theory, so that we
       don't "overload" the ` = ` connective with two syntax definitions.  This
       is done to prevent ambiguity that would complicate some Metamath
       parsers.  For example, some parsers - although not the Metamath program
       - stumble on the fact that the ` = ` in ` x = y ` could be the ` = ` of
       either ~ weq or ~ wceq , although mathematically it makes no
       difference.  The exp variables ` A ` and ` B ` are introduced
       temporarily for the purpose of this definition but otherwise not used in
       predicate calculus.  See ~ df-cleq for more information on the set
       theory usage of ~ wceq .) $)
    wceq $a wff A = B $.
  $}

  $( Extend wff definition to include atomic formulas using the equality
     predicate.

     (Instead of introducing ~ weq as an axiomatic statement, as was done in an
     older version of this database, we introduce it by "proving" a special
     case of set theory's more general ~ wceq .  This lets us avoid overloading
     the ` = ` connective, thus preventing ambiguity that would complicate
     certain Metamath parsers.  However, logically ~ weq is considered to be a
     primitive syntax, even though here it is artificially "derived" from
     ~ wceq .  Note:  To see the proof steps of this syntax proof, type "show
     proof weq /all" in the Metamath program.) $)
  weq $p wff x = y $=
    ( cv wceq ) ACBCD $.
    $( [24-Jan-2006] $)
  $( --- End of patch to prevent connective overloading $)

  $( --- Start of old code before overloading prevention patch. $)
  $(
  @( Extend wff definition to include atomic formulas using the equality
     predicate.

     After we introduce ~ cv and ~ wceq in set theory, this syntax construction
     becomes redundant, since it can be derived with the proof
     "vx cv vy cv wceq". @)
  weq @a wff x = y @.
  $)
  $( --- End of old code before overloading prevention patch. $)

  $( Declare the membership predicate symbol. $)
  $c e. $. $( Stylized epsilon $)

  $( --- Start of patch to prevent connective overloading $)
  ${
    $v A $.
    $v B $.
    wcel.cA $f exp A $.
    wcel.cB $f exp B $.
    $( Extend wff definition to include the membership connective between
       classes.

       (The purpose of introducing ` wff A e. B ` here is to allow us to
       express i.e.  "prove" the ~ wel of predicate calculus in terms of the
       ~ wceq of set theory, so that we don't "overload" the ` e. ` connective
       with two syntax definitions.  This is done to prevent ambiguity that
       would complicate some Metamath parsers.  The exp variables ` A ` and
       ` B ` are introduced temporarily for the purpose of this definition but
       otherwise not used in predicate calculus.  See ~ df-clab for more
       information on the set theory usage of ~ wcel .) $)
    wcel $a wff A e. B $.
  $}

  $( Extend wff definition to include atomic formulas with the epsilon
     (membership) predicate.  This is read " ` x ` is an element of
     ` y ` ," " ` x ` is a member of ` y ` ," " ` x ` belongs to ` y ` ,"
     or " ` y ` contains ` x ` ."  Note:  The phrase " ` y ` includes
     ` x ` " means " ` x ` is a subset of ` y ` ;" to use it also for
     ` x e. y ` , as some authors occasionally do, is poor form and causes
     confusion, according to George Boolos (1992 lecture at MIT).

     This syntactical construction introduces a binary non-logical predicate
     symbol ` e. ` (epsilon) into our predicate calculus.  We will eventually
     use it for the membership predicate of set theory, but that is irrelevant
     at this point: the predicate calculus axioms for ` e. ` apply to any
     arbitrary binary predicate symbol.  "Non-logical" means that the predicate
     is presumed to have additional properties beyond the realm of predicate
     calculus, although these additional properties are not specified by
     predicate calculus itself but rather by the axioms of a theory (in our
     case set theory) added to predicate calculus.  "Binary" means that the
     predicate has two arguments.

     (Instead of introducing ~ wel as an axiomatic statement, as was done in an
     older version of this database, we introduce it by "proving" a special
     case of set theory's more general ~ wcel .  This lets us avoid overloading
     the ` e. ` connective, thus preventing ambiguity that would complicate
     certain Metamath parsers.  However, logically ~ wel is considered to be a
     primitive syntax, even though here it is artificially "derived" from
     ~ wcel .  Note:  To see the proof steps of this syntax proof, type "show
     proof wel /all" in the Metamath program.) $)
  wel $p wff x e. y $=
    ( cv wcel ) ACBCD $.
    $( [24-Jan-2006] $)
  $( --- End of patch to prevent connective overloading $)

  $( --- Start of old code before overloading prevention patch. $)
  $(
  @( Extend wff definition to include atomic formulas with the epsilon
     (membership) predicate.  This is read " ` x ` is an element of ` y ` ,"
     " ` x ` is a member of ` y ` ," " ` x ` belongs to ` y ` ," or " ` y `
     contains ` x ` ."  Note:  The phrase " ` y ` includes ` x ` " means
     " ` x ` is a subset of ` y ` "; to use it also for ` x e. y ` (as some
     authors occasionally do) is poor form and causes confusion.

     After we introduce ~ cv and ~ wcel in set theory, this syntax construction
     becomes redundant, since it can be derived with the proof
     "vx cv vy cv wcel". @)
  wel @a wff x e. y @.
  $)
  $( --- End of old code before overloading prevention patch. $)

  $( Axiom of Equality.  One of the equality and substitution axioms of
     predicate calculus with equality.  This is similar to, but not quite, a
     transitive law for equality (proved later as ~ equtr ).  Axiom scheme C8'
     in [Megill] p. 448 (p. 16 of the preprint).  Also appears as Axiom C7 of
     [Monk2] p. 105.

     Axioms ~ ax-8 through ~ ax-16 are the axioms having to do with equality,
     substitution, and logical properties of our binary predicate ` e. ` (which
     later in set theory will mean "is a member of").  Note that all axioms
     except ~ ax-16 and ~ ax-17 are still valid even when ` x ` , ` y ` , and
     ` z ` are replaced with the same variable because they do not have any
     distinct variable (Metamath's $d) restrictions.  Distinct variable
     restrictions are required for ~ ax-16 and ~ ax-17 only. $)
  ax-8 $a |- ( x = y -> ( x = z -> y = z ) ) $.

  $( Axiom of Quantifier Substitution.  One of the equality and substitution
     axioms of predicate calculus with equality.  Appears as Lemma L12 in
     [Megill] p. 445 (p. 12 of the preprint).

     The original version of this axiom was ~ ax-10o ("o" for "old") and was
     replaced with this shorter ~ ax-10 in May 2008.  The old axiom is proved
     from this one as theorem ~ ax10o .  Conversely, this axiom is proved from
     ~ ax-10o as theorem ~ ax10 . $)
  ax-10 $a |- ( A. x x = y -> A. y y = x ) $.

  $( Axiom of Variable Substitution.  One of the 5 equality axioms of predicate
     calculus.  The final consequent ` A. x ( x = y -> ph ) ` is a way of
     expressing " ` y ` substituted for ` x ` in wff ` ph ` " (cf. ~ sb6 ).  It
     is based on Lemma 16 of [Tarski] p. 70 and Axiom C8 of [Monk2] p. 105,
     from which it can be proved by cases.

     The original version of this axiom was ~ ax-11o ("o" for "old") and was
     replaced with this shorter ~ ax-11 in Jan. 2007.  The old axiom is proved
     from this one as theorem ~ ax11o .  Conversely, this axiom is proved from
     ~ ax-11o as theorem ~ ax11 .

     Juha Arpiainen proved the independence of this axiom (in the form of the
     older axiom ~ ax-11o ) from the others on 19-Jan-2006.  See item 9a at
     ~ http://us.metamath.org/award2003.html .

     Interestingly, if the wff expression substituted for ` ph ` contains no
     wff variables, the resulting statement _can_ be proved without invoking
     this axiom.  This means that even though this axiom is _metalogically_
     independent from the others, it is not _logically_ independent.
     Specifically, we can prove any wff-variable-free instance of axiom
     ~ ax-11o (from which the ~ ax-11 instance follows by theorem ~ ax11 .)
     The proof is by induction on formula length, using ~ ax11eq and ~ ax11el
     for the basis steps and ~ ax11indn , ~ ax11indi , and ~ ax11inda for the
     induction steps.

     See also ~ ax11v and ~ ax11v2 for other equivalents of this axiom that
     (unlike this axiom) have distinct variable restrictions. $)
  ax-11 $a |- ( x = y -> ( A. y ph -> A. x ( x = y -> ph ) ) ) $.

  $( Axiom of Quantifier Introduction.  One of the equality and substitution
     axioms of predicate calculus with equality.  Informally, it says that
     whenever ` z ` is distinct from ` x ` and ` y ` , and ` x = y ` is true,
     then ` x = y ` quantified with ` z ` is also true.  In other words, ` z `
     is irrelevant to the truth of ` x = y ` .  Axiom scheme C9' in [Megill]
     p. 448 (p. 16 of the preprint).  It apparently does not otherwise appear
     in the literature but is easily proved from textbook predicate calculus by
     cases.

     An open problem is whether this axiom is redundant.  Note that the
     analogous axiom for the membership connective, ~ ax-15 , has been shown to
     be redundant.  It is also unknown whether this axiom can be replaced by a
     shorter formula.  However, it can be derived from two slightly shorter
     formulas, as shown by ~ a12study . $)
  ax-12 $a |- ( -. A. z z = x -> ( -. A. z z = y ->
              ( x = y -> A. z x = y ) ) ) $.

  $( Axiom of Equality.  One of the equality and substitution axioms for a
     non-logical predicate in our predicate calculus with equality.  It
     substitutes equal variables into the left-hand side of the ` e. ` binary
     predicate.  Axiom scheme C12' in [Megill] p. 448 (p. 16 of the preprint).
     It is a special case of Axiom B8 (p. 75) of system S2 of [Tarski] p. 77.
     "Non-logical" means that the predicate is not a primitive of predicate
     calculus proper but instead is an extension to it.  "Binary" means that
     the predicate has two arguments.  In a system of predicate calculus with
     equality, like ours, equality is not usually considered to be a
     non-logical predicate.  In systems of predicate calculus without equality,
     it typically would be. $)
  ax-13 $a |- ( x = y -> ( x e. z -> y e. z ) ) $.

  $( Axiom of Equality.  One of the equality and substitution axioms for a
     non-logical predicate in our predicate calculus with equality.  It
     substitutes equal variables into the right-hand side of the ` e. ` binary
     predicate.  Axiom scheme C13' in [Megill] p. 448 (p. 16 of the preprint).
     It is a special case of Axiom B8 (p. 75) of system S2 of [Tarski]
     p. 77. $)
  ax-14 $a |- ( x = y -> ( z e. x -> z e. y ) ) $.

  $( Bound-variable hypothesis builder for ` x = x ` .  This theorem tells us
     that any variable, including ` x ` , is effectively not free in
     ` x = x ` , even though ` x ` is technically free according to the
     traditional definition of free variable.  (The proof uses only ~ ax-5 ,
     ~ ax-8 , ~ ax-12 , and ~ ax-gen .  This shows that this can be proved
     without ~ ax-9 , even though the theorem ~ equid cannot be.  A shorter
     proof using ~ ax-9 is obtainable from ~ equid and ~ hbth .)  (The proof
     was shortened by Wolf Lammen, 23-Mar-2014.) $)
  hbequid $p |- ( x = x -> A. y x = x ) $=
    ( weq wal wi ax-12 ax-8 pm2.43i alimi a1d pm2.61ii ) BACZBDZMAACZNBDZEAABFM
    ONLNBLNBAAGHIJZPK $.
    $( [23-Mar-2014] $) $( [13-Jan-2011] $)

  $( Obsolete proof of ~ hbequid as of 23-Mar-2014. $)
  hbequidOLD $p |- ( x = x -> A. y x = x ) $=
    ( cv wceq wal wi ax-12 ax-8 pm2.43i ax-gen ax-5 ax-mp a1d pm2.61ii ) BCACZD
    ZBEZQOODZRBEZFAABGQSRPRFZBEQSFTBPRBAAHIJPRBKLMZUAN $.
    $( [13-Jan-2011] $)

  $( Commutation law for identical variable specifiers.  The antecedent and
     consequent are true when ` x ` and ` y ` are substituted with the same
     variable.  Lemma L12 in [Megill] p. 445 (p. 12 of the preprint). $)
  alequcom $p |- ( A. x x = y -> A. y y = x ) $=
    ( ax-10 ) ABC $.
    $( [5-Aug-1993] $)

  ${
    alequcoms.1 $e |- ( A. x x = y -> ph ) $.
    $( A commutation rule for identical variable specifiers. $)
    alequcoms $p |- ( A. y y = x -> ph ) $=
      ( weq wal alequcom syl ) CBECFBCEBFACBGDH $.
      $( [5-Aug-1993] $)
  $}

  ${
    nalequcoms.1 $e |- ( -. A. x x = y -> ph ) $.
    $( A commutation rule for distinct variable specifiers. $)
    nalequcoms $p |- ( -. A. y y = x -> ph ) $=
      ( weq wal alequcom nsyl4 con1i ) ACBECFZBCEBFJABCGDHI $.
      $( [2-Jan-2002] $)
  $}

  $( Lemma used in proofs of substitution properties. $)
  equs3 $p |- ( E. x ( x = y /\ ph ) <-> -. A. x ( x = y -> -. ph ) ) $=
    ( weq wn wi wal wa wex alinexa con2bii ) BCDZAEFBGLAHBILABJK $.
    $( [5-Aug-1993] $)

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Axiom ax-17 - first use of the $d distinct variable statement
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d x ph $.
    $( Axiom to quantify a variable over a formula in which it does not occur.
       Axiom C5 in [Megill] p. 444 (p. 11 of the preprint).  Also appears as
       Axiom B6 (p. 75) of system S2 of [Tarski] p. 77 and Axiom C5-1 of
       [Monk2] p. 113.

       This axiom is _logically_ redundant in the (logically complete)
       predicate calculus axiom system consisting of ~ ax-gen , ~ ax-4 through
       ~ ax-9 , ~ ax-10o , and ~ ax-12 through ~ ax-16 : in that system, we can
       derive any instance of ~ ax-17 not containing wff variables by induction
       on formula length, using ~ ax17eq and ~ ax17el for the basis together
       ~ hbn , ~ hbal , and ~ hbim .  However, if we omit this axiom, our
       development would be quite inconvenient since we could work only with
       specific instances of wffs containing no wff variables - this axiom
       introduces the concept of a set variable not occurring in a wff (as
       opposed to just two set variables being distinct). $)
    ax-17 $a |- ( ph -> A. x ph ) $.
  $}

  ${
    $d x ps $.
    $( ~ ax-17 with antecedent.  Useful in proofs of deduction versions of
       bound-variable hypothesis builders such as ~ hbeleqd . $)
    a17d $p |- ( ph -> ( ps -> A. x ps ) ) $=
      ( wal wi ax-17 a1i ) BBCDEABCFG $.
      $( [1-Mar-2013] $)
  $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Derive ax-9 from a weaker version
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)


  ${
    $d x w $.  $d w z $.
    a9wa9lem1.1 $e |- -. A. w -. w = x $.
    $( Lemma for ~ a9wa9 .  Similar to ~ equcomi , without using ~ ax-9 or
       ~ ax-4 . $)
    a9wa9lem1 $p |- ( x = y -> y = x ) $=
      ( weq wn wal ax-8 pm2.43i con3i alimi mto ax-17 mt3 mpi ) ABEAAEZBAEPPFZC
      GZRCAEZFZCGDQTCSPSPCAAHIJKLQCMNABAHO $.
      $( [12-Nov-2013] $)

    a9wa9lem2.2 $e |- -. A. w -. w = z $.
    $( Lemma for ~ a9wa9 .  Similar to ~ equequ2 , without using ~ ax-9 or
       ~ ax-4 . $)
    a9wa9lem2 $p |- ( x = y -> ( z = x <-> z = y ) ) $=
      ( weq a9wa9lem1 ax-8 com12 syl5 syl2im impbid ) ABGZCAGZCBGZOACGZNPCADFHQ
      NPACBIJKNBAGZPBCGZOABDEHCBDFHSROBCAIJLM $.
      $( [3-Apr-2014] $) $( [12-Nov-2013] $)

    $( Obsolete proof of ~ a9wa9lem2 as of 3-Apr-2014. $)
    a9wa9lem2OLD $p |- ( x = y -> ( z = x <-> z = y ) ) $=
      ( weq wi a9wa9lem1 ax-8 syl com12 syl2im impbid ) ABGZCAGZCBGZPOQPACGOQHC
      ADFIACBJKLOBAGZQBCGZPABDEICBDFISRPBCAJLMN $.
      $( [12-Nov-2013] $)
  $}

  ${
    $d x w $.  $d w ph $.
    a9wa9lem3.1 $e |- -. A. w -. w = x $.
    a9wa9lem3.2 $e |- -. A. x -. x = w $.
    $( Lemma for ~ a9wa9 .  Similar to ~ ax4 , without using ~ ax-9 or
       ~ ax-4 . $)
    a9wa9lem3 $p |- ( A. x ph -> ph ) $=
      ( wal wi weq wn ax-17 a9wa9lem1 ax-11 syl2im con2 al2imi mtoi con4d con3i
      syl6 alrimi mt3 ) ABFZAGZCBHZIZCFDUCIZUECUFCJUDUCUDAUBUDAIZBCHZUGGZBFZUBI
      UDUHUGUGCFUJCBBEKUGCJUGBCLMUJUBUHIZBFEUIAUKBUHANOPSQRTUA $.
      $( [12-Nov-2013] $)

    $( Lemma for ~ a9wa9 .  Similar to ~ hba1 , without using ~ ax-9 or
       ~ ax-4 . $)
    a9wa9lem4 $p |- ( A. x ph -> A. x A. x ph ) $=
      ( wal wn a9wa9lem3 con2i ax-6 con1i alimi 3syl ) ABFZNGZBFZGZQBFNBFPNOBCD
      EHIOBJQNBNPABJKLM $.
      $( [12-Nov-2013] $)

    a9wa9lem5.3 $e |- ( ph -> A. x ph ) $.
    $( Lemma for ~ a9wa9 .  Similar to ~ hbn , without using ~ ax-9 or
       ~ ax-4 . $)
    a9wa9lem5 $p |- ( -. ph -> A. x -. ph ) $=
      ( wn wal a9wa9lem3 con3i ax-6 alrimi syl ) AGZABHZGZNBHOAABCDEIJPNBABKAOF
      JLM $.
      $( [12-Nov-2013] $)
  $}

  ${
    $d x w $.  $d w ph $.  $d w ps $.
    a9wa9lem6.1 $e |- -. A. w -. w = x $.
    a9wa9lem6.2 $e |- -. A. x -. x = w $.
    a9wa9lem6.3 $e |- ( ph -> A. x ph ) $.
    a9wa9lem6.4 $e |- ( ph -> ( ps -> A. x ps ) ) $.
    a9wa9lem6.5 $e |- ( ph -> ( ch -> A. x ch ) ) $.
    $( Lemma for ~ a9wa9 .  Similar to ~ hbimd , without using ~ ax-9 or
       ~ ax-4 .  (The proof was shortened by Wolf Lammen, 3-Apr-2014.) $)
    a9wa9lem6 $p |- ( ph -> ( ( ps -> ch ) -> A. x ( ps -> ch ) ) ) $=
      ( wi wal wn alrimi a9wa9lem3 ax-6 nsyl4 con1i alimi syl6 con3 al2imi ax-1
      syl2im pm2.21 jad ) ABCBCKZDLZABMZUIDLZUHABBDLZKZDLUIUKMZDLZUJAULDHINUNBU
      KBUNBDEFGOBDPQRULUMUIDBUKUAUBUDUIUGDBCUESTACCDLUHJCUGDCBUCSTUF $.
      $( [3-Apr-2014] $) $( [12-Nov-2013] $)

    $( Obsolete proof of ~ a9wa9lem6 as of 3-Apr-2014. $)
    a9wa9lem6OLD $p |- ( ph -> ( ( ps -> ch ) -> A. x ( ps -> ch ) ) ) $=
      ( wi wal wn alrimi a9wa9lem3 ax-6 nsyl4 con1i alimi syl6com al2imi syl2im
      con3 pm2.21 ax-1 ja com12 ) BCKZAUHDLZBCAUIKABMZUJDLZUIABBDLZKZDLUJULMZDL
      ZUKAUMDHINUOBULBUOBDEFGOBDPQRUMUNUJDBULUCUAUBUJUHDBCUDSTACCDLUIJCUHDCBUES
      TUFUG $.
      $( [12-Nov-2013] $)
  $}

  ${
    $d x w $.  $d w ph $.  $d w ps $.
    a9wa9lem7.1 $e |- -. A. w -. w = x $.
    a9wa9lem7.2 $e |- -. A. x -. x = w $.
    a9wa9lem7.3 $e |- ( ph -> A. x ph ) $.
    a9wa9lem7.4 $e |- ( ps -> A. x ps ) $.
    $( Lemma for ~ a9wa9 .  Similar to ~ hban , without using ~ ax-9 or
       ~ ax-4 . $)
    a9wa9lem7 $p |- ( ( ph /\ ps ) -> A. x ( ph /\ ps ) ) $=
      ( wa wn wi df-an wal a9wa9lem5 pm2.21 alrimi ax-1 ja hbxfrbi ) ABIABJZKZJ
      CABLUACDEFATUACMAJUACACDEFGNATOPTUACBCDEFHNTAQPRNS $.
      $( [12-Nov-2013] $)
  $}

  ${
    $d x v w z $.  $d y v w z $.  $d w x ph $.  $d w z ps $.
    a9wa9.1 $e |- -. A. w -. w = x $.
    a9wa9.2 $e |- -. A. x -. x = w $.
    a9wa9.3 $e |- -. A. z -. z = y $.
    a9wa9.4 $e |- -. A. w -. w = z $.
    a9wa9.5 $e |- -. A. z -. z = w $.

    ${
      a9wa9lem8.6 $e |- ( z = y -> ( ph <-> ps ) ) $.
      $( Lemma for ~ a9wa9 .  Similar to ~ dvelimfALT , without using ~ ax-9 or
         ~ ax-4 .  (The proof was shortened by Wolf Lammen, 18-Jul-2014.) $)
      a9wa9lem8 $p |- ( -. A. x x = y -> ( ps -> A. x ps ) ) $=
        ( weq wal wn wi ax-17 alrimi alimi ax-6 a1d a9wa9lem3 syl5ibr a2i ax-10
        wa syl con3i nalequcoms a9wa9lem7 ax-12 imp a17d a9wa9lem6 hbald biimpd
        con3 al2imi mtoi con1i 3syl syl56 expcom ax-11 syl2im pm2.27 pm2.61d2
        syld ) CDMZCNOZCEMZCNZBBCNZPZVLOZVJVNBEDMZAPZENZVOVJUFZVRCNVMBVPBENZPZE
        NVRBWAEBEQZBVTVPWBUARWAVQEVPVTAVTAVPBBEFJKUBLUCUDSUGVSVQCEVOVJEFJKVOENE
        CECMZENZOVOEWCETVLWDCEUEUHRUIVJEQUJVSVPACFGHVOVJCFGHVKCTVICTUJVOVJVPVPC
        NPEDCUKULVSACUMUNUOVRBCVRVPBPZENZBOZENZOBVQWEEVPABVPABLUPUDSWFWHVPOZENI
        WEWGWIEVPBUQURUSBWHWGEQUTVASVBVCVLBVKBPZCNZVMVLVKBVTWKVKCFGHUBWBBCEVDVE
        VKWJBCVKBVFURVHVG $.
        $( [18-Jul-2014] $) $( [12-Nov-2013] $)

      $( Obsolete proof of ~ a9wa9lem8 as of 18-Jul-2014. $)
      a9wa9lem8OLD $p |- ( -. A. x x = y -> ( ps -> A. x ps ) ) $=
        ( weq wi wal wn ax-17 a1d alimi ax-6 alrimi a9wa9lem3 syl5ibr a9wa9lem4
        a2i syl ax-11 pm2.27 al2imi syld ax-10 con3i nalequcoms a9wa9lem7 ax-12
        syl5 wa imp a17d a9wa9lem6 hbald ex pm2.61i biimpd con3 mtoi con1i 3syl
        syl56 ) BEDMZANZEOZCDMZCOPZVLCOZBCOBVJBEOZNZEOVLBVQEBEQZBVPVJVRRUAVQVKE
        VJVPAVPAVJBBEFJKUBLUCUESUFCEMZCOZVNVLVONZNVTWAVNVLVLEOZVTVOVKEFJKUDVTWB
        VSVLNZCOZVOVTVSWBWDNVSCFGHUBVLCEUGUFVSWCVLCVSVLUHUIUJUPRVTPZVNWAWEVNUQZ
        VKCEWEVNEFJKWEEOECECMZEOZPWEEWGETVTWHCEUKULUAUMVNEQUNWFVJACFGHWEVNCFGHV
        SCTVMCTUNWEVNVJVJCONEDCUOURWFACUSUTVAVBVCVLBCVLVJBNZEOZBPZEOZPBVKWIEVJA
        BVJABLVDUESWJWLVJPZEOIWIWKWMEVJBVEUIVFBWLWKEQVGVHSVI $.
        $( [12-Nov-2013] $)
    $}

    a9wa9.6 $e |- -. A. v -. v = y $.
    a9wa9.7 $e |- -. A. w -. w = v $.
    a9wa9.8 $e |- -. A. x -. x = v $.
    $( Derive ~ ax-9 (which has no distinct variable requirement) from a weaker
       version that requires that its two variables be distinct.  The
       hypotheses are the instances of the weaker version that we need.
       Neither ~ ax-9 nor ~ ax-4 (which can be derived from ~ ax-9 ) is used by
       the proof.  Note that every other predicate calculus axiom (except
       ~ ax-13 and ~ ax-14 ) is used by the proof.  (The proof was shortened by
       Wolf Lammen, 28-Mar-2014.) $)
    a9wa9 $p |- -. A. x -. x = y $=
      ( weq wal wn a9wa9lem3 nsyl3 wi a9wa9lem2 ax-17 a9wa9lem8 a9wa9lem4 albid
      wb syl notbid mtbii syl6com con3i alrimi mt3 pm2.61i ) ABNZAOZUNPZAOZPZUQ
      UNUOUPADFGQUNADFGQRUOPZURSZEBNZPZEOKUTPZVBEVCEUAVAUTUSVAVAAOZURECNVAABCDF
      GHIJCBEDILTUBVDAENZPZAOUQMVDVFUPAVAADFGUCVDVEUNVDVAVEUNUEVAADFGQEBADLFTUF
      UGUDUHUIUJUKULUM $.
      $( [28-Mar-2014] $) $( [12-Nov-2013] $)

    $( Obsolete proof of ~ a9wa9 as of 28-Mar-2014. $)
    a9wa9OLD $p |- -. A. x -. x = y $=
      ( cv wceq wal wn a9wa9lem3 syl a9wa9lem2 con2i a9wa9lem8 a9wa9lem4 notbid
      wi ax-17 wb albid mpbii syl6com con3i alrimi mt3 pm2.61i ) ANZBNZOZAPZUQQ
      ZAPZQZURUQVAUQADFGRUTUQUSADFGRUASURQZVAUEZENZUPOZQZEPKVCQZVFEVGEUFVEVCVBV
      EVEAPZVAVDCNOVEABCDFGHIJCBEDILTUBVHUOVDOZQZAPZQVAMVHVKUTVHVJUSAVEADFGUCVH
      VIUQVHVEVIUQUGVEADFGREBADLFTSUDUHUDUIUJUKULUMUN $.
      $( [12-Nov-2013] $)
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Introduce Axiom of Existence ax-9
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Axiom of Existence.  One of the equality and substitution axioms of
     predicate calculus with equality.  One thing this axiom tells us is that
     at least one thing exists (although ~ ax-4 and possibly others also tell
     us that, i.e. they are not valid in the empty domain of a "free logic").
     In this form (not requiring that ` x ` and ` y ` be distinct) it was used
     in an axiom system of Tarski (see Axiom B7' in footnote 1 of
     [KalishMontague] p. 81.)  It is equivalent to axiom scheme C10' in
     [Megill] p. 448 (p. 16 of the preprint); the equivalence is established by
     ~ ax9o and ~ ax9 .  A more convenient form of this axiom is ~ a9e , which
     has additional remarks.

     Raph Levien proved the independence of this axiom from the other logical
     axioms on 12-Apr-2005.  See item 16 at
     ~ http://us.metamath.org/award2003.html .

     ~ ax-9 can be proved from a weaker version requiring that the variables be
     distinct; see theorem ~ a9wa9 .

     ~ ax-9 can also be proved from the Axiom of Separation.  See theorem
     ~ ax9sep .  Thus ~ ax-9 is dispensable for Zermelo set theory Z, which
     uses the the Axiom of Separation instead of the Axiom of Replacement. $)
  ax-9 $a |- -. A. x -. x = y $.

  $( ~ equid with existential quantifier without using ~ ax-4 or ~ ax-17 .
     (The proof was shortened by Wolf Lammen, 27-Feb-2014.) $)
  equidqe $p |- -. A. y -. x = x $=
    ( weq wn wal ax-9 ax-8 pm2.43i con3i alimi mto ) AACZDZBEBACZDZBEBAFMOBNLNL
    BAAGHIJK $.
    $( [27-Feb-2014] $) $( [13-Jan-2011] $)

  $( Obsolete proof of ~ equidqe as of 27-Feb-2014. $)
  equidqeOLD $p |- -. A. y -. x = x $=
    ( weq wn wal ax-9 wi ax-8 pm2.43i con3i ax-gen ax-5 ax-mp mto ) AACZDZBEZBA
    CZDZBEZBAFPSGZBEQTGUABROROBAAHIJKPSBLMN $.
    $( [13-Jan-2011] $)

  $( ~ equid with universal quantifier without using ~ ax-4 or ~ ax-17 . $)
  equidq $p |- A. y x = x $=
    ( weq wal wn equidqe ax-6 hbequid con3i alrimi mt3 ) AACZBDZLEZBDABFMENBLBG
    LMABHIJK $.
    $( [13-Jan-2011] $)

  $( A special case of ~ ax-4 without using ~ ax-4 or ~ ax-17 . $)
  ax4sp1 $p |- ( A. y -. x = x -> -. x = x ) $=
    ( weq wn wal equidqe pm2.21i ) AACDZBEHABFG $.
    $( [13-Jan-2011] $)


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Derive ax-4, ax-5o, and ax-6o
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d x y $.  $d y ph $.
    $( Theorem showing that ~ ax-4 can be derived from ~ ax-5 , ~ ax-gen ,
       ~ ax-8 , ~ ax-9 , ~ ax-11 , and ~ ax-17 and is therefore redundant in a
       system including these axioms.  The proof uses ideas from the proof of
       Lemma 21 of [Monk2] p. 114.

       This theorem should not be referenced in any proof.  Instead, we will
       use ~ ax-4 below so that explicit uses of ~ ax-4 can be more easily
       identified.  In particular, this will more cleanly separate out the
       theorems of "pure" predicate calculus that don't involve equality or
       distinct variables.  A beginner may wish to accept ~ ax-4 a priori, so
       that the proof of this theorem ( ~ ax4 ), which involves equality as
       well as the distinct variable requirements of ~ ax-17 , can be put off
       until those axioms are studied.

       Note:  All predicate calculus axioms introduced from this point forward
       are redundant.  Immediately before their introduction, we prove them
       from earlier axioms to demonstrate their redundancy.  Specifically,
       redundant axioms ~ ax-4 , ~ ax-5o , ~ ax-6o , ~ ax-9o , ~ ax-10o ,
       ~ ax-11o , ~ ax-15 , and ~ ax-16 are proved by theorems ~ ax4 , ~ ax5o ,
       ~ ax6o , ~ ax9o , ~ ax10o , ~ ax11o , ~ ax15 , and ~ ax16 .  Except for
       the ones suffixed with o ( ~ ax-5o etc.), we never reference those
       theorems directly.  Instead, we use the axiom version that immediately
       follows it.  This allow us to better isolate the uses of the redundant
       axioms for easier study of subsystems containing them.

       (The proof was shortened by Scott Fenton, 24-Jan-2011.) $)
    ax4 $p |- ( A. x ph -> ph ) $=
      ( vy wal wi weq ax-9 ax-8 pm2.43i con3i ax-gen ax-17 ax-5 mpsyl mt3 ax-11
      wn mpi syl2im con2 ax-mp syl mtoi syl6 con4d ) ABDZAEZCBFZQZCDZCBGUGQZUIE
      ZCDUKUKCDUJULCUHUGUHAUFUHAQZBCFZUMEZBDZUFQUHUNUMUMCDUPUHCCFZUNUQUNQZBDZBC
      GZUQQZUREZBDVAVABDUSVBBUNUQUNUQBCCHIJKVABLVAURBMNOCBCHRUMCLUMBCPSUPUFUSUT
      UPAUREZBDZUFUSEUOVCEZBDUPVDEVEBUNATKUOVCBMUAAURBMUBUCUDUEJKUKCLUKUICMNO
      $.
      $( [24-Jan-2011] $) $( [21-May-2008] $)
  $}

  $( Axiom of Specialization.  A quantified wff implies the wff without a
     quantifier (i.e. an instance, or special case, of the generalized wff).
     In other words if something is true for all ` x ` , it is true for any
     specific ` x ` (that would typically occur as a free variable in the wff
     substituted for ` ph ` ).  (A free variable is one that does not occur in
     the scope of a quantifier: ` x ` and ` y ` are both free in ` x = y ` ,
     but only ` x ` is free in ` A. y x = y ` .)  This is one of the axioms of
     what we call "pure" predicate calculus ( ~ ax-4 through ~ ax-7 plus rule
     ~ ax-gen ).  Axiom scheme C5' in [Megill] p. 448 (p. 16 of the preprint).
     Also appears as Axiom B5 of [Tarski] p. 67 (under his system S2, defined
     in the last paragraph on p. 77).

     Note that the converse of this axiom does not hold in general, but a
     weaker inference form of the converse holds and is expressed as rule
     ~ ax-gen .  Conditional forms of the converse are given by ~ ax-12 ,
     ~ ax-15 , ~ ax-16 , and ~ ax-17 .

     Unlike the more general textbook Axiom of Specialization, we cannot choose
     a variable different from ` x ` for the special case.  For use, that
     requires the assistance of equality axioms, and we deal with it later
     after we introduce the definition of proper substitution - see ~ stdpc4 .

     An nice alternate axiomatization uses ~ ax467 and ~ ax-5o in place of
     ~ ax-4 , ~ ax-5 , ~ ax-6 , and ~ ax-7 .

     This axiom is redundant in the presence of certain other axioms, as shown
     by theorem ~ ax4 .  (We replaced the older ~ ax-5o and ~ ax-6o with newer
     versions ~ ax-5 and ~ ax-6 in order to prove this redundancy.) $)
  ax-4 $a |- ( A. x ph -> ph ) $.

  $( Show that the original axiom ~ ax-5o can be derived from ~ ax-5 and
     others.  See ~ ax5 for the rederivation of ~ ax-5 from ~ ax-5o .

     Part of the proof is based on the proof of Lemma 22 of [Monk2] p. 114.

     Normally, ~ ax5o should be used rather than ~ ax-5o , except by theorems
     specifically studying the latter's properties. $)
  ax5o $p |- ( A. x ( A. x ph -> ps ) -> ( A. x ph -> A. x ps ) ) $=
    ( wal wi wn ax-4 con2i ax-6 con1i ax-gen ax-5 ax-mp 3syl syl5 ) ACDZPCDZPBE
    CDBCDPPFZCDZFZTCDZQSPRCGHRCITPEZCDUAQEUBCPSACIJKTPCLMNPBCLO $.
    $( [21-May-2008] $)

  $( Axiom of Quantified Implication.  This axiom moves a quantifier from
     outside to inside an implication, quantifying ` ps ` .  Notice that ` x `
     must not be a free variable in the antecedent of the quantified
     implication, and we express this by binding ` ph ` to "protect" the axiom
     from a ` ph ` containing a free ` x ` .  One of the 4 axioms of "pure"
     predicate calculus.  Axiom scheme C4' in [Megill] p. 448 (p. 16 of the
     preprint).  It is a special case of Lemma 5 of [Monk2] p. 108 and Axiom 5
     of [Mendelson] p. 69.

     This axiom is redundant, as shown by theorem ~ ax5o .

     Normally, ~ ax5o should be used rather than ~ ax-5o , except by theorems
     specifically studying the latter's properties. $)
  ax-5o $a |- ( A. x ( A. x ph -> ps ) -> ( A. x ph -> A. x ps ) ) $.

  $( Rederivation of axiom ~ ax-5 from the orginal version, ~ ax-5o .  See
     ~ ax5o for the derivation of ~ ax-5o from ~ ax-5 .

     This theorem should not be referenced in any proof.  Instead, use ~ ax-5
     above so that uses of ~ ax-5 can be more easily identified.

     Note:  This is the same as theorem ~ alim below.  It is proved separately
     here so that it won't be dependent on the axioms used for ~ alim . $)
  ax5 $p |- ( A. x ( ph -> ps ) -> ( A. x ph -> A. x ps ) ) $=
    ( wi wal ax-4 syl5 ax-gen ax-5o ax-mp syl ) ABDZCEZACEZBDZCEZNBCEDMODZCEMPD
    QCNAMBACFLCFGHLOCIJABCIK $.
    $( [5-Dec-2010] $) $( [23-May-2008] $)

  $( Show that the original axiom ~ ax-6o can be derived from ~ ax-6 and
     others.  See ~ ax6 for the rederivation of ~ ax-6 from ~ ax-6o .

     Normally, ~ ax6o should be used rather than ~ ax-6o , except by theorems
     specifically studying the latter's properties. $)
  ax6o $p |- ( -. A. x -. A. x ph -> ph ) $=
    ( wal wn ax-4 ax-6 nsyl4 ) ABCZAHDBCABEABFG $.
    $( [21-May-2008] $)

  $( Axiom of Quantified Negation.  This axiom is used to manipulate negated
     quantifiers.  One of the 4 axioms of pure predicate calculus.  Equivalent
     to axiom scheme C7' in [Megill] p. 448 (p. 16 of the preprint).  An
     alternate axiomatization could use ~ ax467 in place of ~ ax-4 , ~ ax-6o ,
     and ~ ax-7 .

     This axiom is redundant, as shown by theorem ~ ax6o .

     Normally, ~ ax6o should be used rather than ~ ax-6o , except by theorems
     specifically studying the latter's properties. $)
  ax-6o $a |- ( -. A. x -. A. x ph -> ph ) $.

  $( Rederivation of axiom ~ ax-6 from the orginal version, ~ ax-6o .  See
     ~ ax6o for the derivation of ~ ax-6o from ~ ax-6 .

     This theorem should not be referenced in any proof.  Instead, use ~ ax-6
     above so that uses of ~ ax-6 can be more easily identified. $)
  ax6 $p |- ( -. A. x ph -> A. x -. A. x ph ) $=
    ( wal wn wi ax-4 id ax-gen ax-5o ax-mp nsyl ax-6o nsyl4 ) ABCZBCZDZBCZNDZBC
    ZNQREZBCQSETBQONPBFNNEZBCNOEUABNGHANBIJKHPRBIJNBLM $.
    $( [23-May-2008] $)

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
    "Pure" predicate calculus including ax-4, without distinct variables
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)


  ${
    a4i.1 $e |- A. x ph $.
    $( Inference rule reversing generalization. $)
    a4i $p |- ph $=
      ( wal ax-4 ax-mp ) ABDACABEF $.
      $( [5-Aug-1993] $)
  $}

  ${
    a4s.1 $e |- ( ph -> ps ) $.
    $( Generalization of antecedent. $)
    a4s $p |- ( A. x ph -> ps ) $=
      ( wal ax-4 syl ) ACEABACFDG $.
      $( [5-Aug-1993] $)
  $}

  ${
    a4sd.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Deduction generalizing antecedent. $)
    a4sd $p |- ( ph -> ( A. x ps -> ch ) ) $=
      ( wal ax-4 syl5 ) BDFBACBDGEH $.
      $( [17-Aug-1994] $)
  $}

  $( Abbreviated version of ~ ax-6o . $)
  a6e $p |- ( E. x A. x ph -> ph ) $=
    ( wal wex wn df-ex ax6o sylbi ) ABCZBDIEBCEAIBFABGH $.
    $( [5-Aug-1993] $)

  $( Closed theorem version of bound-variable hypothesis builder ~ hbn . $)
  hbnt $p |- ( A. x ( ph -> A. x ph ) -> ( -. ph -> A. x -. ph ) ) $=
    ( wn wal wi ax6o con1i con3 al2imi syl5 ) ACZABDZCZBDZALEZBDKBDNAABFGOMKBAL
    HIJ $.
    $( [5-Aug-1993] $)

  $( ` x ` is not free in ` A. x ph ` .  Example in Appendix in [Megill] p. 450
     (p. 19 of the preprint).  Also Lemma 22 of [Monk2] p. 114. $)
  hba1 $p |- ( A. x ph -> A. x A. x ph ) $=
    ( wal wn ax-4 con2i ax-6 con1i alimi 3syl ) ABCZKDZBCZDZNBCKBCMKLBEFLBGNKBK
    MABGHIJ $.
    $( [5-Aug-1993] $)

  ${
    a5i.1 $e |- ( A. x ph -> ps ) $.
    $( Inference version of ~ ax-5o . $)
    a5i $p |- ( A. x ph -> A. x ps ) $=
      ( wal wi hba1 ax-5 syl5 mpg ) ACEZBFZKBCEZFCKKCELCEMACGKBCHIDJ $.
      $( [5-Aug-1993] $)
  $}

  ${
    hb.1 $e |- ( ph -> A. x ph ) $.
    $( If ` x ` is not free in ` ph ` , it is not free in ` -. ph ` . $)
    hbn $p |- ( -. ph -> A. x -. ph ) $=
      ( wal wi wn hbnt mpg ) AABDEAFZIBDEBABGCH $.
      $( [5-Aug-1993] $)

    $( If ` x ` is not free in ` ph ` , it is not free in ` E. y ph ` . $)
    hbex $p |- ( E. y ph -> A. x E. y ph ) $=
      ( wex wn wal df-ex hbn hbal hbxfrbi ) ACEAFZCGZFBACHMBLBCABDIJIK $.
      $( [5-Aug-1993] $)

    ${
      hb.2 $e |- ( ps -> A. x ps ) $.
      $( If ` x ` is not free in ` ph ` and ` ps ` , it is not free in
         ` ( ph -> ps ) ` .  (The proof was shortened by O'Cat, 3-Mar-2008.) $)
      hbim $p |- ( ( ph -> ps ) -> A. x ( ph -> ps ) ) $=
        ( wi wal wn hbn pm2.21 alrimi ax-1 ja ) ABABFZCGAHNCACDIABJKBNCEBALKM
        $.
        $( [4-Mar-2008] $)  $( [5-Aug-1993] $)

      $( If ` x ` is not free in ` ph ` and ` ps ` , it is not free in
         ` ( ph \/ ps ) ` . $)
      hbor $p |- ( ( ph \/ ps ) -> A. x ( ph \/ ps ) ) $=
        ( wo wn wi df-or hbn hbim hbxfrbi ) ABFAGZBHCABIMBCACDJEKL $.
        $( [5-Aug-1993] $)

      $( If ` x ` is not free in ` ph ` and ` ps ` , it is not free in
         ` ( ph /\ ps ) ` . $)
      hban $p |- ( ( ph /\ ps ) -> A. x ( ph /\ ps ) ) $=
        ( wa wn wi df-an hbn hbim hbxfrbi ) ABFABGZHZGCABINCAMCDBCEJKJL $.
        $( [5-Aug-1993] $)

      $( If ` x ` is not free in ` ph ` and ` ps ` , it is not free in
         ` ( ph <-> ps ) ` . $)
      hbbi $p |- ( ( ph <-> ps ) -> A. x ( ph <-> ps ) ) $=
        ( wb wi wa dfbi2 hbim hban hbxfrbi ) ABFABGZBAGZHCABIMNCABCDEJBACEDJKL
        $.
        $( [5-Aug-1993] $)

      ${
        hb.3 $e |- ( ch -> A. x ch ) $.
        $( If ` x ` is not free in ` ph ` , ` ps ` , and ` ch ` , it is not
           free in ` ( ph \/ ps \/ ch ) ` . $)
        hb3or $p |- ( ( ph \/ ps \/ ch ) -> A. x ( ph \/ ps \/ ch ) ) $=
          ( w3o wo df-3or hbor hbxfrbi ) ABCHABIZCIDABCJMCDABDEFKGKL $.
          $( [14-Sep-2003] $)

        $( If ` x ` is not free in ` ph ` , ` ps ` , and ` ch ` , it is not
           free in ` ( ph /\ ps /\ ch ) ` . $)
        hb3an $p |- ( ( ph /\ ps /\ ch ) -> A. x ( ph /\ ps /\ ch ) ) $=
          ( w3a wa df-3an hban hbxfrbi ) ABCHABIZCIDABCJMCDABDEFKGKL $.
          $( [14-Sep-2003] $)
      $}
    $}
  $}

  $( Lemma 24 of [Monk2] p. 114. $)
  hba2 $p |- ( A. y A. x ph -> A. x A. y A. x ph ) $=
    ( wal hba1 hbal ) ABDBCABEF $.
    $( [29-May-2008] $)

  $( Lemma 23 of [Monk2] p. 114. $)
  hbia1 $p |- ( ( A. x ph -> A. x ps ) -> A. x ( A. x ph -> A. x ps ) ) $=
    ( wal hba1 hbim ) ACDBCDCACEBCEF $.
    $( [29-May-2008] $)

  $( Obsolete proof of ~ hbn1 as of 15-Aug-2014. $)
  hbn1OLD $p |- ( -. A. x ph -> A. x -. A. x ph ) $=
    ( wal hba1 hbn ) ABCBABDE $.
    $( [5-Aug-1993] $)

  $( ` x ` is not free in ` -. A. x ph ` .  (The proof was shortened by Wolf
     Lammen, 18-Aug-2014.) $)
  hbn1 $p |- ( -. A. x ph -> A. x -. A. x ph ) $=
    ( ax-6 ) ABC $.
    $( [18-Aug-2014] $) $( [5-Aug-1993] $)

  $( ` x ` is not free in ` E. x ph ` . $)
  hbe1 $p |- ( E. x ph -> A. x E. x ph ) $=
    ( wex wn wal df-ex hbn1 hbxfrbi ) ABCADZBEDBABFIBGH $.
    $( [5-Aug-1993] $)

  $( Proof of a single axiom that can replace ~ ax-4 and ~ ax-6o .  See
     ~ ax46to4 and ~ ax46to6 for the re-derivation of those axioms.
     (Contributed by Scott Fenton, 12-Sep-2005.) $)
  ax46 $p |- ( ( A. x -. A. x ph -> A. x ph ) -> ph ) $=
    ( wal wn ax-6o ax-4 ja ) ABCZDBCHAABEABFG $.
    $( [12-Sep-2005] $)

  $( Re-derivation of ~ ax-4 from ~ ax46 .  Only propositional calculus is used
     for the re-derivation.  (Contributed by Scott Fenton, 12-Sep-2005.) $)
  ax46to4 $p |- ( A. x ph -> ph ) $=
    ( wal wn wi ax-1 ax46 syl ) ABCZIDBCZIEAIJFABGH $.
    $( [12-Sep-2005] $)

  $( Re-derivation of ~ ax-6o from ~ ax46 .  Only propositional calculus is
     used for the re-derivation.  (Contributed by Scott Fenton,
     12-Sep-2005.) $)
  ax46to6 $p |- ( -. A. x -. A. x ph -> ph ) $=
    ( wal wn wi pm2.21 ax46 syl ) ABCZDBCZDJIEAJIFABGH $.
    $( [12-Sep-2005] $)

  $( Proof of a single axiom that can replace both ~ ax-6o and ~ ax-7 .  See
     ~ ax67to6 and ~ ax67to7 for the re-derivation of those axioms. $)
  ax67 $p |- ( -. A. x -. A. y A. x ph -> A. y ph ) $=
    ( wal wn ax-7 con3i alimi ax-6o syl ) ABDCDZEZBDZEACDZBDZEZBDZENQMPLBKOACBF
    GHGNBIJ $.
    $( [18-Nov-2006] $)

  $( Re-derivation of ~ ax-6o from ~ ax67 .  Note that ~ ax-6o and ~ ax-7 are
     not used by the re-derivation. $)
  ax67to6 $p |- ( -. A. x -. A. x ph -> ph ) $=
    ( wal wn hba1 con3i alimi ax67 ax-4 3syl ) ABCZDZBCZDKBCZDZBCZDKAPMOLBKNABE
    FGFABBHABIJ $.
    $( [18-Nov-2006] $)

  $( Re-derivation of ~ ax-7 from ~ ax67 .  Note that ~ ax-6o and ~ ax-7 are
     not used by the re-derivation. $)
  ax67to7 $p |- ( A. x A. y ph -> A. y A. x ph ) $=
    ( wal wn ax67to6 con4i ax67 alimi syl ) ACDBDZKEZCDEZCDZABDZCDNKLCFGMOCACBH
    IJ $.
    $( [18-Nov-2006] $)

  $( Proof of a single axiom that can replace ~ ax-4 , ~ ax-6o , and ~ ax-7 in
     a subsystem that includes these axioms plus ~ ax-5o and ~ ax-gen (and
     propositional calculus).  See ~ ax467to4 , ~ ax467to6 , and ~ ax467to7 for
     the re-derivation of those axioms.  This theorem extends the idea in Scott
     Fenton's ~ ax46 . $)
  ax467 $p |- ( ( A. x A. y -. A. x A. y ph -> A. x ph ) -> ph ) $=
    ( wal wn ax-4 hbn1 ax-6o con1i alimi ax-7 3syl nsyl4 ja ) ACDZBDEZCDBDZABDA
    OAQACFOEZRCDPBDZCDQACGRSCSOOBHIJPCBKLMABFN $.
    $( [18-Nov-2006] $)

  $( Re-derivation of ~ ax-4 from ~ ax467 .  Only propositional calculus is
     used by the re-derivation. $)
  ax467to4 $p |- ( A. x ph -> ph ) $=
    ( wal wn wi ax-1 ax467 syl ) ABCZIBCDBCBCZIEAIJFABBGH $.
    $( [19-Nov-2006] $)

  $( Re-derivation of ~ ax-6o from ~ ax467 .  Note that ~ ax-6o and ~ ax-7 are
     not used by the re-derivation.  The use of ~ alimi (which uses ~ ax-4 ) is
     allowed since we have already proved ~ ax467to4 . $)
  ax467to6 $p |- ( -. A. x -. A. x ph -> ph ) $=
    ( wal wn wi ax467to4 hba1 con3i alimi syl pm2.21 ax467 3syl ) ABCZDZBCZDNBC
    ZDZBCZBCZDTNEATPTSPSBFROBNQABGHIJHTNKABBLM $.
    $( [19-Nov-2006] $)

  $( Re-derivation of ~ ax-7 from ~ ax467 .  Note that ~ ax-6o and ~ ax-7 are
     not used by the re-derivation.  The use of ~ alimi (which uses ~ ax-4 ) is
     allowed since we have already proved ~ ax467to4 . $)
  ax467to7 $p |- ( A. x A. y ph -> A. y A. x ph ) $=
    ( wal wn ax467to6 con4i wi pm2.21 ax467 syl alimi nsyl4 ) ACDBDZNEZCDZEZCDZ
    ABDZCDRNOCFGQSCPBDZEZBDSPUAABUATSHATSIABCJKLPBFMLK $.
    $( [19-Nov-2006] $)

  $( The analog in our "pure" predicate calculus of axiom 5 of modal logic
     S5. $)
  modal-5 $p |- ( -. A. x -. ph -> A. x -. A. x -. ph ) $=
    ( wn hbn1 ) ACBD $.
    $( [5-Oct-2005] $)

  $( The analog in our "pure" predicate calculus of the Brouwer axiom (B) of
     modal logic S5. $)
  modal-b $p |- ( ph -> A. x -. A. x -. ph ) $=
    ( wn wal ax6o con4i ) ACZBDCBDAGBEF $.
    $( [5-Oct-2005] $)

  $( If a wff is true, it is true for at least one instance.  Special case of
     Theorem 19.8 of [Margaris] p. 89. $)
  19.8a $p |- ( ph -> E. x ph ) $=
    ( wn wal wex ax-4 con2i df-ex sylibr ) AACZBDZCABEKAJBFGABHI $.
    $( [5-Aug-1993] $)

  $( Theorem 19.2 of [Margaris] p. 89, generalized to use two set variables.
     (Contributed by O'Cat, 31-Mar-2008.) $)
  19.2 $p |- ( A. x ph -> E. y ph ) $=
    ( wex 19.8a a4s ) AACDBACEF $.
    $( [31-Mar-2008] $)

  ${
    19.3.1 $e |- ( ph -> A. x ph ) $.
    $( A wff may be quantified with a variable not free in it.  Theorem 19.3 of
       [Margaris] p. 89. $)
    19.3 $p |- ( A. x ph <-> ph ) $=
      ( wal ax-4 impbii ) ABDAABECF $.
      $( [21-May-2007] $) $( [5-Aug-1993] $)
  $}

  $( A closed version of one direction of ~ 19.9 . $)
  19.9t $p |- ( A. x ( ph -> A. x ph ) -> ( E. x ph -> ph ) ) $=
    ( wex wn wal wi df-ex hbnt con1d syl5bi ) ABCADBEZDAABEFBEZAABGLAKABHIJ $.
    $( [5-Aug-1993] $)

  ${
    19.9.1 $e |- ( ph -> A. x ph ) $.
    $( A wff may be existentially quantified with a variable not free in it.
       Theorem 19.9 of [Margaris] p. 89.  (Contributed by FL, 24-Mar-2007.) $)
    19.9 $p |- ( E. x ph <-> ph ) $=
      ( wex wal wi 19.9t mpg 19.8a impbii ) ABDZAAABEFKAFBABGCHABIJ $.
      $( [24-Mar-2007] $)
  $}

  ${
    19.9d.1 $e |- ( ps -> A. x ps ) $.
    19.9d.2 $e |- ( ps -> ( ph -> A. x ph ) ) $.
    $( A deduction version of one direction of ~ 19.9 . $)
    19.9d $p |- ( ps -> ( E. x ph -> ph ) ) $=
      ( wal wi wex alimi 19.9t 3syl ) BBCFAACFGZCFACHAGDBLCEIACJK $.
      $( [5-Aug-1993] $)
  $}

  $( One direction of Theorem 19.11 of [Margaris] p. 89. $)
  excomim $p |- ( E. x E. y ph -> E. y E. x ph ) $=
    ( wex 19.8a 2eximi hbe1 hbex 19.9 sylib ) ACDBDABDZCDZBDLAKBCABEFLBKBCABGHI
    J $.
    $( [5-Aug-1993] $)

  $( Theorem 19.11 of [Margaris] p. 89. $)
  excom $p |- ( E. x E. y ph <-> E. y E. x ph ) $=
    ( wex excomim impbii ) ACDBDABDCDABCEACBEF $.
    $( [5-Aug-1993] $)

  $( Theorem 19.12 of [Margaris] p. 89.  Assuming the converse is a mistake
     sometimes made by beginners!  But sometimes the converse does hold, as in
     ~ 19.12vv and ~ r19.12sn . $)
  19.12 $p |- ( E. x A. y ph -> A. y E. x ph ) $=
    ( wal wex hba1 hbex ax-4 eximi alrimi ) ACDZBEABECKCBACFGKABACHIJ $.
    $( [5-Aug-1993] $)

  ${
    19.16.1 $e |- ( ph -> A. x ph ) $.
    $( Theorem 19.16 of [Margaris] p. 90. $)
    19.16 $p |- ( A. x ( ph <-> ps ) -> ( ph <-> A. x ps ) ) $=
      ( wal wb 19.3 albi syl5bbr ) AACEABFCEBCEACDGABCHI $.
      $( [5-Aug-1993] $)
  $}

  ${
    19.17.1 $e |- ( ps -> A. x ps ) $.
    $( Theorem 19.17 of [Margaris] p. 90. $)
    19.17 $p |- ( A. x ( ph <-> ps ) -> ( A. x ph <-> ps ) ) $=
      ( wb wal albi 19.3 syl6bb ) ABECFACFBCFBABCGBCDHI $.
      $( [5-Aug-1993] $)
  $}

  ${
    19.19.1 $e |- ( ph -> A. x ph ) $.
    $( Theorem 19.19 of [Margaris] p. 90. $)
    19.19 $p |- ( A. x ( ph <-> ps ) -> ( ph <-> E. x ps ) ) $=
      ( wex wb wal 19.9 exbi syl5bbr ) AACEABFCGBCEACDHABCIJ $.
      $( [5-Aug-1993] $)
  $}

  ${
    19.21.1 $e |- ( ph -> A. x ph ) $.
    $( Theorem 19.21 of [Margaris] p. 90.  The hypothesis can be thought of
       as " ` x ` is not free in ` ph ` ." $)
    19.21 $p |- ( A. x ( ph -> ps ) <-> ( ph -> A. x ps ) ) $=
      ( wi wal alim syl5 hba1 hbim ax-4 imim2i alrimi impbii ) ABEZCFZABCFZEZAA
      CFPQDABCGHROCAQCDBCIJQBABCKLMN $.
      $( [5-Aug-1993] $)
  $}

  ${
    19.21-2.1 $e |- ( ph -> A. x ph ) $.
    19.21-2.2 $e |- ( ph -> A. y ph ) $.
    $( Theorem 19.21 of [Margaris] p. 90 but with 2 quantifiers. $)
    19.21-2 $p |- ( A. x A. y ( ph -> ps ) <-> ( ph -> A. x A. y ps ) ) $=
      ( wi wal 19.21 albii bitri ) ABGDHZCHABDHZGZCHAMCHGLNCABDFIJAMCEIK $.
      $( [4-Feb-2005] $)
  $}

  ${
    stdpc5.1 $e |- ( ph -> A. x ph ) $.
    $( An axiom scheme of standard predicate calculus that emulates Axiom 5 of
       [Mendelson] p. 69.  The hypothesis ` ( ph -> A. x ph ) ` can be thought
       of as emulating " ` x ` is not free in ` ph ` ."  With this convention,
       the meaning of "not free" is less restrictive than the usual textbook
       definition; for example ` x ` would not (for us) be free in ` x = x ` by
       ~ hbequid .  This theorem scheme can be proved as a metatheorem of
       Mendelson's axiom system, even though it is slightly stronger than his
       Axiom 5. $)
    stdpc5 $p |- ( A. x ( ph -> ps ) -> ( ph -> A. x ps ) ) $=
      ( wi wal 19.21 biimpi ) ABECFABCFEABCDGH $.
      $( [22-Sep-1993] $)
  $}

  ${
    19.21bi.1 $e |- ( ph -> A. x ps ) $.
    $( Inference from Theorem 19.21 of [Margaris] p. 90. $)
    19.21bi $p |- ( ph -> ps ) $=
      ( wal ax-4 syl ) ABCEBDBCFG $.
      $( [5-Aug-1993] $)
  $}

  ${
    19.21bbi.1 $e |- ( ph -> A. x A. y ps ) $.
    $( Inference removing double quantifier. $)
    19.21bbi $p |- ( ph -> ps ) $=
      ( wal 19.21bi ) ABDABDFCEGG $.
      $( [20-Apr-1994] $)
  $}

  ${
    19.23.1 $e |- ( ps -> A. x ps ) $.
    $( Theorem 19.23 of [Margaris] p. 90. $)
    19.23 $p |- ( A. x ( ph -> ps ) <-> ( E. x ph -> ps ) ) $=
      ( wi wal wex exim 19.9 syl6ib hbe1 hbim 19.8a imim1i alrimi impbii ) ABEZ
      CFZACGZBEZRSBCGBABCHBCDIJTQCSBCACKDLASBACMNOP $.
      $( [5-Aug-1993] $)
  $}

  ${
    exlimi.1 $e |- ( ps -> A. x ps ) $.
    exlimi.2 $e |- ( ph -> ps ) $.
    $( Inference from Theorem 19.23 of [Margaris] p. 90.  (The proof was
       shortened by Andrew Salmon, 13-May-2011.) $)
    exlimi $p |- ( E. x ph -> ps ) $=
      ( wi wex 19.23 mpgbi ) ABFACGBFCABCDHEI $.
      $( [16-May-2011] $) $( [5-Aug-1993] $)
  $}

  ${
    19.23bi.1 $e |- ( E. x ph -> ps ) $.
    $( Inference from Theorem 19.23 of [Margaris] p. 90. $)
    19.23bi $p |- ( ph -> ps ) $=
      ( wex 19.8a syl ) AACEBACFDG $.
      $( [5-Aug-1993] $)
  $}

  ${
    exlimd.1 $e |- ( ph -> A. x ph ) $.
    exlimd.2 $e |- ( ch -> A. x ch ) $.
    exlimd.3 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Deduction from Theorem 19.23 of [Margaris] p. 90. $)
    exlimd $p |- ( ph -> ( E. x ps -> ch ) ) $=
      ( wi wal wex alrimi 19.23 sylib ) ABCHZDIBDJCHANDEGKBCDFLM $.
      $( [28-Jan-1997] $)
  $}

  ${
    19.27.1 $e |- ( ps -> A. x ps ) $.
    $( Theorem 19.27 of [Margaris] p. 90. $)
    19.27 $p |- ( A. x ( ph /\ ps ) <-> ( A. x ph /\ ps ) ) $=
      ( wa wal 19.26 19.3 anbi2i bitri ) ABECFACFZBCFZEKBEABCGLBKBCDHIJ $.
      $( [5-Aug-1993] $)
  $}

  ${
    19.28.1 $e |- ( ph -> A. x ph ) $.
    $( Theorem 19.28 of [Margaris] p. 90. $)
    19.28 $p |- ( A. x ( ph /\ ps ) <-> ( ph /\ A. x ps ) ) $=
      ( wa wal 19.26 19.3 anbi1i bitri ) ABECFACFZBCFZEALEABCGKALACDHIJ $.
      $( [5-Aug-1993] $)
  $}

  ${
    19.36.1 $e |- ( ps -> A. x ps ) $.
    $( Theorem 19.36 of [Margaris] p. 90. $)
    19.36 $p |- ( E. x ( ph -> ps ) <-> ( A. x ph -> ps ) ) $=
      ( wi wex wal 19.35 19.9 imbi2i bitri ) ABECFACGZBCFZELBEABCHMBLBCDIJK $.
      $( [5-Aug-1993] $)
  $}

  ${
    19.36i.1 $e |- ( ps -> A. x ps ) $.
    19.36i.2 $e |- E. x ( ph -> ps ) $.
    $( Inference from Theorem 19.36 of [Margaris] p. 90. $)
    19.36i $p |- ( A. x ph -> ps ) $=
      ( wi wex wal 19.36 mpbi ) ABFCGACHBFEABCDIJ $.
      $( [5-Aug-1993] $)
  $}

  ${
    19.37.1 $e |- ( ph -> A. x ph ) $.
    $( Theorem 19.37 of [Margaris] p. 90. $)
    19.37 $p |- ( E. x ( ph -> ps ) <-> ( ph -> E. x ps ) ) $=
      ( wi wex wal 19.35 19.3 imbi1i bitri ) ABECFACGZBCFZEAMEABCHLAMACDIJK $.
      $( [5-Aug-1993] $)
  $}

  $( Theorem 19.38 of [Margaris] p. 90. $)
  19.38 $p |- ( ( E. x ph -> A. x ps ) -> A. x ( ph -> ps ) ) $=
    ( wex wal wi hbe1 hba1 hbim 19.8a ax-4 imim12i alrimi ) ACDZBCEZFABFCNOCACG
    BCHIANOBACJBCKLM $.
    $( [5-Aug-1993] $)

  $( Theorem 19.39 of [Margaris] p. 90. $)
  19.39 $p |- ( ( E. x ph -> E. x ps ) -> E. x ( ph -> ps ) ) $=
    ( wex wi wal 19.2 imim1i 19.35 sylibr ) ACDZBCDZEACFZLEABECDMKLACCGHABCIJ
    $.
    $( [5-Aug-1993] $)

  $( Theorem 19.24 of [Margaris] p. 90. $)
  19.24 $p |- ( ( A. x ph -> A. x ps ) -> E. x ( ph -> ps ) ) $=
    ( wal wi wex 19.2 imim2i 19.35 sylibr ) ACDZBCDZEKBCFZEABECFLMKBCCGHABCIJ
    $.
    $( [5-Aug-1993] $)

  ${
    19.32.1 $e |- ( ph -> A. x ph ) $.
    $( Theorem 19.32 of [Margaris] p. 90. $)
    19.32 $p |- ( A. x ( ph \/ ps ) <-> ( ph \/ A. x ps ) ) $=
      ( wn wi wal wo hbn 19.21 df-or albii 3bitr4i ) AEZBFZCGNBCGZFABHZCGAPHNBC
      ACDIJQOCABKLAPKM $.
      $( [5-Aug-1993] $)
  $}

  ${
    19.31.1 $e |- ( ps -> A. x ps ) $.
    $( Theorem 19.31 of [Margaris] p. 90. $)
    19.31 $p |- ( A. x ( ph \/ ps ) <-> ( A. x ph \/ ps ) ) $=
      ( wo wal 19.32 orcom albii 3bitr4i ) BAEZCFBACFZEABEZCFLBEBACDGMKCABHILBH
      J $.
      $( [5-Aug-1993] $)
  $}

  ${
    19.44.1 $e |- ( ps -> A. x ps ) $.
    $( Theorem 19.44 of [Margaris] p. 90. $)
    19.44 $p |- ( E. x ( ph \/ ps ) <-> ( E. x ph \/ ps ) ) $=
      ( wo wex 19.43 19.9 orbi2i bitri ) ABECFACFZBCFZEKBEABCGLBKBCDHIJ $.
      $( [5-Aug-1993] $)
  $}

  ${
    19.45.1 $e |- ( ph -> A. x ph ) $.
    $( Theorem 19.45 of [Margaris] p. 90. $)
    19.45 $p |- ( E. x ( ph \/ ps ) <-> ( ph \/ E. x ps ) ) $=
      ( wo wex 19.43 19.9 orbi1i bitri ) ABECFACFZBCFZEALEABCGKALACDHIJ $.
      $( [5-Aug-1993] $)
  $}

  $( Theorem 19.34 of [Margaris] p. 90. $)
  19.34 $p |- ( ( A. x ph \/ E. x ps ) -> E. x ( ph \/ ps ) ) $=
    ( wal wex wo 19.2 orim1i 19.43 sylibr ) ACDZBCEZFACEZLFABFCEKMLACCGHABCIJ
    $.
    $( [5-Aug-1993] $)

  ${
    19.41.1 $e |- ( ps -> A. x ps ) $.
    $( Theorem 19.41 of [Margaris] p. 90.  (The proof was shortened by Andrew
       Salmon, 25-May-2011.) $)
    19.41 $p |- ( E. x ( ph /\ ps ) <-> ( E. x ph /\ ps ) ) $=
      ( wa wex 19.40 id exlimi anim2i syl pm3.21 eximd impcom impbii ) ABEZCFZA
      CFZBEZQRBCFZESABCGTBRBBCDBHIJKBRQBAPCDBALMNO $.
      $( [25-May-2011] $) $( [5-Aug-1993] $)
  $}

  ${
    19.42.1 $e |- ( ph -> A. x ph ) $.
    $( Theorem 19.42 of [Margaris] p. 90. $)
    19.42 $p |- ( E. x ( ph /\ ps ) <-> ( ph /\ E. x ps ) ) $=
      ( wa wex 19.41 exancom ancom 3bitr4i ) BAECFBCFZAEABECFAKEBACDGABCHAKIJ
      $.
      $( [18-Aug-1993] $)
  $}

  $( Swap 1st and 3rd existential quantifiers. $)
  excom13 $p |- ( E. x E. y E. z ph <-> E. z E. y E. x ph ) $=
    ( wex excom exbii 3bitri ) ADEZCEBEIBEZCEABEZDEZCEKCEDEIBCFJLCABDFGKCDFH $.
    $( [9-Mar-1995] $)

  $( Rotate existential quantifiers. $)
  exrot3 $p |- ( E. x E. y E. z ph <-> E. y E. z E. x ph ) $=
    ( wex excom13 excom bitri ) ADECEBEABEZCEDEIDECEABCDFIDCGH $.
    $( [17-Mar-1995] $)

  $( Rotate existential quantifiers twice. $)
  exrot4 $p |- ( E. x E. y E. z E. w ph <-> E. z E. w E. x E. y ph ) $=
    ( wex excom13 exbii bitri ) AEFDFCFZBFACFZDFEFZBFKBFEFDFJLBACDEGHKBEDGI $.
    $( [9-Mar-1995] $)

  ${
    nexr.1 $e |- -. E. x ph $.
    $( Inference from ~ 19.8a .  (Contributed by Jeff Hankins, 26-Jul-2009.) $)
    nexr $p |- -. ph $=
      ( wex 19.8a mto ) AABDCABEF $.
      $( [26-Jul-2009] $)
  $}

  ${
    hbim1.1 $e |- ( ph -> A. x ph ) $.
    hbim1.2 $e |- ( ph -> ( ps -> A. x ps ) ) $.
    $( A closed form of ~ hbim . $)
    hbim1 $p |- ( ( ph -> ps ) -> A. x ( ph -> ps ) ) $=
      ( wi wal a2i 19.21 sylibr ) ABFZABCGZFKCGABLEHABCDIJ $.
      $( [5-Aug-1993] $)
  $}

  ${
    exan.1 $e |- ( E. x ph /\ ps ) $.
    $( Place a conjunct in the scope of an existential quantifier.  (The proof
       was shortened by Andrew Salmon, 25-May-2011.) $)
    exan $p |- E. x ( ph /\ ps ) $=
      ( wex wal wa hbe1 19.28 mpgbi 19.29r ax-mp ) ACEZBCFGZABGCEMBGNCMBCACHIDJ
      ABCKL $.
      $( [25-May-2011] $) $( [18-Aug-1993] $)
  $}

  ${
    hbnd.1 $e |- ( ph -> A. x ph ) $.
    hbnd.2 $e |- ( ph -> ( ps -> A. x ps ) ) $.
    $( Deduction form of bound-variable hypothesis builder ~ hbn . $)
    hbnd $p |- ( ph -> ( -. ps -> A. x -. ps ) ) $=
      ( wal wi wn alrimi hbnt syl ) ABBCFGZCFBHZMCFGALCDEIBCJK $.
      $( [3-Jan-2002] $)
  $}

  ${
    hbimd.1 $e |- ( ph -> A. x ph ) $.
    hbimd.2 $e |- ( ph -> ( ps -> A. x ps ) ) $.
    hbimd.3 $e |- ( ph -> ( ch -> A. x ch ) ) $.
    $( Deduction form of bound-variable hypothesis builder ~ hbim . $)
    hbimd $p |- ( ph -> ( ( ps -> ch ) -> A. x ( ps -> ch ) ) ) $=
      ( wi wal wn hbnd pm2.21 alimi syl6com ax-1 ja com12 ) BCHZARDIZBCASHABJZT
      DISABDEFKTRDBCLMNACCDISGCRDCBOMNPQ $.
      $( [1-Jan-2002] $)
  $}

  ${
    hbbid.1 $e |- ( ph -> A. x ph ) $.
    hbbid.2 $e |- ( ph -> ( ps -> A. x ps ) ) $.
    hbbid.3 $e |- ( ph -> ( ch -> A. x ch ) ) $.
    $( Deduction form of bound-variable hypothesis builder ~ hbbi . $)
    hbbid $p |- ( ph -> ( ( ps <-> ch ) -> A. x ( ps <-> ch ) ) ) $=
      ( wi wa wal wb hbimd anim12d dfbi2 albiim 3imtr4g ) ABCHZCBHZIQDJZRDJZIBC
      KZUADJAQSRTABCDEFGLACBDEGFLMBCNBCDOP $.
      $( [1-Jan-2002] $)
  $}

  ${
    hbexd.1 $e |- ( ph -> A. y ph ) $.
    hbexd.2 $e |- ( ph -> ( ps -> A. x ps ) ) $.
    $( Deduction form of bound-variable hypothesis builder ~ hbex . $)
    hbexd $p |- ( ph -> ( E. y ps -> A. x E. y ps ) ) $=
      ( wex wal eximd 19.12 syl6 ) ABDGZBCHZDGLCHABMDEFIBDCJK $.
      $( [2-Jan-2002] $)
  $}

  $( Closed form of Theorem 19.21 of [Margaris] p. 90. $)
  19.21t $p |- ( A. x ( ph -> A. x ph ) ->
               ( A. x ( ph -> ps ) <-> ( ph -> A. x ps ) ) ) $=
    ( wal wi alim imim2d com12 a4s hba1 ax-4 a1i hbimd imim2i alimi syl6 impbid
    ) AACDZEZCDZABEZCDZABCDZEZSUBUDECUBSUDUBRUCAABCFGHITUDUDCDUBTAUCCSCJSCKUCUC
    CDETBCJLMUDUACUCBABCKNOPQ $.
    $( [27-May-1997] $)

  $( Closed form of Theorem 19.23 of [Margaris] p. 90. $)
  19.23t $p |- ( A. x ( ps -> A. x ps ) ->
               ( A. x ( ph -> ps ) <-> ( E. x ph -> ps ) ) ) $=
    ( wal wi wex hba1 ax-4 impbid2 imbi2d albid 19.23 syl5bb bitr3d ) BBCDZEZCD
    ZAOEZCDZABEZCDACFZBEZQRTCPCGQOBAQOBBCHPCHIZJKSUAOEQUBAOCBCGLQOBUAUCJMN $.
    $( [7-Nov-2005] $)

  ${
    aaan.1 $e |- ( ph -> A. y ph ) $.
    aaan.2 $e |- ( ps -> A. x ps ) $.
    $( Rearrange universal quantifiers. $)
    aaan $p |- ( A. x A. y ( ph /\ ps ) <-> ( A. x ph /\ A. y ps ) ) $=
      ( wa wal 19.28 albii hbal 19.27 bitri ) ABGDHZCHABDHZGZCHACHOGNPCABDEIJAO
      CBCDFKLM $.
      $( [12-Aug-1993] $)
  $}

  ${
    eeor.1 $e |- ( ph -> A. y ph ) $.
    eeor.2 $e |- ( ps -> A. x ps ) $.
    $( Rearrange existential quantifiers. $)
    eeor $p |- ( E. x E. y ( ph \/ ps ) <-> ( E. x ph \/ E. y ps ) ) $=
      ( wo wex 19.45 exbii hbex 19.44 bitri ) ABGDHZCHABDHZGZCHACHOGNPCABDEIJAO
      CBCDFKLM $.
      $( [8-Aug-1994] $)
  $}

  $( Quantified "excluded middle."  Exercise 9.2a of Boolos, p. 111,
     _Computability and Logic_. $)
  qexmid $p |- E. x ( ph -> A. x ph ) $=
    ( wal 19.8a 19.35ri ) AABCZBFBDE $.
    $( [10-Dec-2000] $)

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
              Equality theorems without distinct variables
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Show that the original axiom ~ ax-9o can be derived from ~ ax-9 and
     others.  See ~ ax9 for the rederivation of ~ ax-9 from ~ ax-9o .

     Normally, ~ ax9o should be used rather than ~ ax-9o , except by theorems
     specifically studying the latter's properties. $)
  ax9o $p |- ( A. x ( x = y -> A. x ph ) -> ph ) $=
    ( weq wal wi wn ax-9 con3 al2imi mtoi ax-4 ax-6 nsyl4 syl ) BCDZABEZFZBEZQG
    ZBEZGASUAPGZBEBCHRTUBBPQIJKQAUAABLABMNO $.
    $( [5-Aug-1993] $)

  $( A variant of ~ ax-9 .  Axiom scheme C10' in [Megill] p. 448 (p. 16 of the
     preprint).

     This axiom is redundant, as shown by theorem ~ ax9o .

     Normally, ~ ax9o should be used rather than ~ ax-9o , except by theorems
     specifically studying the latter's properties. $)
  ax-9o $a |- ( A. x ( x = y -> A. x ph ) -> ph ) $.

  $( Rederivation of axiom ~ ax-9 from the orginal version, ~ ax-9o .  See
     ~ ax9o for the derivation of ~ ax-9o from ~ ax-9 .  Lemma L18 in [Megill]
     p. 446 (p. 14 of the preprint).

     This theorem should not be referenced in any proof.  Instead, use ~ ax-9
     above so that uses of ~ ax-9 can be more easily identified. $)
  ax9 $p |- -. A. x -. x = y $=
    ( weq wn wal wi ax-9o modal-b mpg ) ABCZJDAEDZAEFKAKABGJAHI $.
    $( [5-Aug-1993] $)

  $( At least one individual exists.  This is not a theorem of free logic,
     which is sound in empty domains.  For such a logic, we would add this
     theorem as an axiom of set theory (Axiom 0 of [Kunen] p. 10).  In the
     system consisting of ~ ax-5 through ~ ax-14 and ~ ax-17 , all axioms other
     than ~ ax-9 are believed to be theorems of free logic, although the system
     without ~ ax-9 is probably not complete in free logic. $)
  a9e $p |- E. x x = y $=
    ( weq wex wn wal ax-9 df-ex mpbir ) ABCZADJEAFEABGJAHI $.
    $( [5-Aug-1993] $)

  $( Identity law for equality (reflexivity).  Lemma 6 of [Tarski] p. 68.  This
     is often an axiom of equality in textbook systems, but we don't need it as
     an axiom since it can be proved from our other axioms (although the proof,
     as you can see below, is not as obvious as you might think).  This proof
     uses only axioms without distinct variable conditions and thus requires no
     dummy variables.  A simpler proof, similar to Tarki's, is possible if we
     make use of ~ ax-17 ; see the proof of ~ equid1 .  See ~ equidALT for an
     alternate proof. $)
  equid $p |- x = x $=
    ( weq wal wn ax-9 hbn1 wi ax-12 pm2.43i con3d alrimi mt3 a4i ) AABZANACZNDZ
    ACAAEODZPANAFQPQNOQNOGAAAHIJIKLM $.
    $( [30-Nov-2008] $)

  $( Identity law for equality (reflexivity).  Lemma 6 of [Tarski] p. 68.
     Alternate proof of ~ equid from older axioms ~ ax-6o and ~ ax-9o . $)
  equidALT $p |- x = x $=
    ( weq wal wn wi ax-12 pm2.43i alimi ax-9o syl ax-6o pm2.61i ) AABZACZDZACZM
    PMNEZACMOQAOQAAAFGHMAAIJMAKL $.
    $( [5-Aug-1993] $)

  ${
    $d x y $.
    $( Identity law for equality (reflexivity).  Lemma 6 of [Tarski] p. 68.
       This proof is similar to Tarski's and makes use of a dummy variable
       ` y ` .  See ~ equid for a proof that avoids dummy variables (but is
       less intuitive). $)
    equid1 $p |- x = x $=
      ( vy weq wex a9e ax-17 ax-8 pm2.43i exlimi ax-mp ) BACZBDAACZBAEKLBLBFKLB
      AAGHIJ $.
      $( [1-Apr-2005] $)
  $}

  $( One of the two equality axioms of standard predicate calculus, called
     reflexivity of equality.  (The other one is ~ stdpc7 .)  Axiom 6 of
     [Mendelson] p. 95.  Mendelson doesn't say why he prepended the redundant
     quantifier, but it was probably to be compatible with free logic (which is
     valid in the empty domain). $)
  stdpc6 $p |- A. x x = x $=
    ( weq equid ax-gen ) AABAACD $.
    $( [16-Feb-2005] $)

  $( Commutative law for equality.  Lemma 7 of [Tarski] p. 69. $)
  equcomi $p |- ( x = y -> y = x ) $=
    ( weq equid1 ax-8 mpi ) ABCAACBACADABAEF $.
    $( [5-Aug-1993] $)

  $( Commutative law for equality. $)
  equcom $p |- ( x = y <-> y = x ) $=
    ( weq equcomi impbii ) ABCBACABDBADE $.
    $( [20-Aug-1993] $)

  ${
    equcoms.1 $e |- ( x = y -> ph ) $.
    $( An inference commuting equality in antecedent.  Used to eliminate the
       need for a syllogism. $)
    equcoms $p |- ( y = x -> ph ) $=
      ( weq equcomi syl ) CBEBCEACBFDG $.
      $( [5-Aug-1993] $)
  $}

  $( A transitive law for equality. $)
  equtr $p |- ( x = y -> ( y = z -> x = z ) ) $=
    ( weq wi ax-8 equcoms ) BCDACDEBABACFG $.
    $( [23-Aug-1993] $)

  $( A transitive law for equality.  Lemma L17 in [Megill] p. 446 (p. 14 of the
     preprint). $)
  equtrr $p |- ( x = y -> ( z = x -> z = y ) ) $=
    ( weq equtr com12 ) CADABDCBDCABEF $.
    $( [23-Aug-1993] $)

  $( A transitive law for equality.  (The proof was shortened by Andrew Salmon,
     25-May-2011.) $)
  equtr2 $p |- ( ( x = z /\ y = z ) -> x = y ) $=
    ( weq wi equtrr equcoms impcom ) BCDACDZABDZIJECBCBAFGH $.
    $( [25-May-2011] $) $( [12-Aug-1993] $)

  $( An equivalence law for equality. $)
  equequ1 $p |- ( x = y -> ( x = z <-> y = z ) ) $=
    ( weq ax-8 equtr impbid ) ABDACDBCDABCEABCFG $.
    $( [5-Aug-1993] $)

  $( An equivalence law for equality. $)
  equequ2 $p |- ( x = y -> ( z = x <-> z = y ) ) $=
    ( weq equtrr wi equcoms impbid ) ABDCADZCBDZABCEJIFBABACEGH $.
    $( [5-Aug-1993] $)

  $( An identity law for the non-logical predicate. $)
  elequ1 $p |- ( x = y -> ( x e. z <-> y e. z ) ) $=
    ( weq wel ax-13 wi equcoms impbid ) ABDACEZBCEZABCFKJGBABACFHI $.
    $( [5-Aug-1993] $)

  $( An identity law for the non-logical predicate. $)
  elequ2 $p |- ( x = y -> ( z e. x <-> z e. y ) ) $=
    ( weq wel ax-14 wi equcoms impbid ) ABDCAEZCBEZABCFKJGBABACFHI $.
    $( [5-Aug-1993] $)

  ${
    ax11i.1 $e |- ( x = y -> ( ph <-> ps ) ) $.
    ax11i.2 $e |- ( ps -> A. x ps ) $.
    $( Inference that has ~ ax-11 (without ` A. y ` ) as its conclusion and
       doesn't require ~ ax-10 , ~ ax-11 , or ~ ax-12 for its proof.  The
       hypotheses may be eliminable without one or more of these axioms in
       special cases.  Proof similar to Lemma 16 of [Tarski] p. 70. $)
    ax11i $p |- ( x = y -> ( ph -> A. x ( x = y -> ph ) ) ) $=
      ( weq wi wal biimprcd alrimi syl6bi ) CDGZABMAHZCIEBNCFMABEJKL $.
      $( [20-May-2008] $)
  $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                  Axioms ax-10 and ax-11
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Show that ~ ax-10o can be derived from ~ ax-10 .  An open problem is
     whether this theorem can be derived from ~ ax-10 and the others when
     ~ ax-11 is replaced with ~ ax-11o .  See theorem ~ ax10 for the
     rederivation of ~ ax-10 from ~ ax10o .

     Normally, ~ ax10o should be used rather than ~ ax-10o , except by theorems
     specifically studying the latter's properties. $)
  ax10o $p |- ( A. x x = y -> ( A. x ph -> A. y ph ) ) $=
    ( weq wal wi ax-10 ax-11 equcoms a4s pm2.27 al2imi sylsyld ) BCDZBECBDZCEAB
    EZOAFZCEZACEBCGNPRFZBSCBACBHIJOQACOAKLM $.
    $( [16-May-2008] $)

  $( Axiom ~ ax-10o ("o" for "old") was the original version of ~ ax-10 ,
     before it was discovered (in May 2008) that the shorter ~ ax-10 could
     replace it.  It appears as Axiom scheme C11' in [Megill] p. 448 (p. 16 of
     the preprint).

     This axiom is redundant, as shown by theorem ~ ax10o .

     Normally, ~ ax10o should be used rather than ~ ax-10o , except by theorems
     specifically studying the latter's properties. $)
  ax-10o $a |- ( A. x x = y -> ( A. x ph -> A. y ph ) ) $.

  $( Rederivation of ~ ax-10 from original version ~ ax-10o .  See theorem
     ~ ax10o for the derivation of ~ ax-10o from ~ ax-10 .

     This theorem should not be referenced in any proof.  Instead, use ~ ax-10
     above so that uses of ~ ax-10 can be more easily identified. $)
  ax10 $p |- ( A. x x = y -> A. y y = x ) $=
    ( weq wal ax-10o pm2.43i equcomi alimi syl ) ABCZADZJBDZBACZBDKLJABEFJMBABG
    HI $.
    $( [16-May-2008] $)

  $( All variables are effectively bound in an identical variable specifier. $)
  hbae $p |- ( A. x x = y -> A. z A. x x = y ) $=
    ( weq wal wi ax-4 ax-12 syl7 ax10o alequcoms pm2.43i syl5 pm2.61ii a5i ax-7
    wn syl ) ABDZAEZSCEZAETCESUAACADCEZCBDCEZTUAFZTSUBQUCQUASAGABCHIUDACSACJKUD
    BCTSBEZBCDBEUATUESABJLSBCJMKNOSACPR $.
    $( [5-Aug-1993] $)

  ${
    hbalequs.1 $e |- ( A. z A. x x = y -> ph ) $.
    $( Rule that applies ~ hbae to antecedent. $)
    hbaes $p |- ( A. x x = y -> ph ) $=
      ( weq wal hbae syl ) BCFBGZJDGABCDHEI $.
      $( [5-Aug-1993] $)
  $}

  $( All variables are effectively bound in a distinct variable specifier.
     Lemma L19 in [Megill] p. 446 (p. 14 of the preprint). $)
  hbnae $p |- ( -. A. x x = y -> A. z -. A. x x = y ) $=
    ( weq wal hbae hbn ) ABDAECABCFG $.
    $( [5-Aug-1993] $)

  ${
    hbnalequs.1 $e |- ( A. z -. A. x x = y -> ph ) $.
    $( Rule that applies ~ hbnae to antecedent. $)
    hbnaes $p |- ( -. A. x x = y -> ph ) $=
      ( weq wal wn hbnae syl ) BCFBGHZKDGABCDIEJ $.
      $( [5-Aug-1993] $)
  $}

  $( Lemma used in proofs of substitution properties.  (The proof was shortened
     by Mario Carneiro, 20-May-2014.) $)
  equs4 $p |- ( A. x ( x = y -> ph ) -> E. x ( x = y /\ ph ) ) $=
    ( cv wceq wi wal wa wex a9e 19.29 mpan2 ancl imp eximi syl ) BDCDEZAFZBGZRQ
    HZBIZQAHZBISQBIUABCJRQBKLTUBBRQUBQAMNOP $.
    $( [20-May-2014] $) $( [5-Aug-1993] $)

  ${
    equsal.1 $e |- ( ps -> A. x ps ) $.
    equsal.2 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( A useful equivalence related to substitution.  (The proof was shortened
       by Andrew Salmon, 12-Aug-2011.) $)
    equsal $p |- ( A. x ( x = y -> ph ) <-> ps ) $=
      ( weq wi wal 19.3 syl6bbr pm5.74i albii a1d alrimi ax9o impbii bitr4i ) C
      DGZAHZCISBCIZHZCIZBTUBCSAUASABUAFBCEJKLMBUCBUBCEBUASENOBCDPQR $.
      $( [12-Aug-2011] $) $( [5-Aug-1993] $)
  $}

  ${
    equsex.1 $e |- ( ps -> A. x ps ) $.
    equsex.2 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( A useful equivalence related to substitution. $)
    equsex $p |- ( E. x ( x = y /\ ph ) <-> ps ) $=
      ( weq wn wi wex wal exnal df-an exbii hbn notbid equsal con2bii 3bitr4i
      wa ) CDGZAHZIZHZCJUCCKZHUAATZCJBUCCLUFUDCUAAMNUEBUBBHCDBCEOUAABFPQRS $.
      $( [5-Aug-1993] $)
  $}

  ${
    dvelimfALT.1 $e |- ( ph -> A. x ph ) $.
    dvelimfALT.2 $e |- ( ps -> A. z ps ) $.
    dvelimfALT.3 $e |- ( z = y -> ( ph <-> ps ) ) $.
    $( Proof of ~ dvelimf that uses ~ ax-10o (in the form of ~ ax10o ) but not
       ~ ax-11o , ~ ax-10 , or ~ ax-11 (if we replace uses of ~ ax10o by
       ~ ax-10o in the proofs of referenced theorems).  See ~ dvelimALT for a
       proof (of the distinct variable version ~ dvelim ) that doesn't require
       ~ ax-10 .  It is not clear whether a proof is possible that uses ~ ax-10
       but avoids ~ ax-11 , ~ ax-11o , and ~ ax-10o . $)
    dvelimfALT $p |- ( -. A. x x = y -> ( ps -> A. x ps ) ) $=
      ( weq wal wn wi hba1 ax10o alequcoms syl5 a1d wa hbnae hban ax-12 imp a1i
      hbimd hbald ex pm2.61i equsal albii 3imtr3g ) CDICJKZEDIZALZEJZUNCJZBBCJC
      EICJZUKUNUOLZLUPUQUKUNUNEJZUPUOUMEMURUOLECUNECNOPQUPKZUKUQUSUKRZUMCEUSUKE
      CEESCDESTUTULACUSUKCCECSCDCSTUSUKULULCJLEDCUAUBAACJLUTFUCUDUEUFUGABEDGHUH
      ZUNBCVAUIUJ $.
      $( [12-Nov-2002] $)
  $}

  ${
    dral1.1 $e |- ( A. x x = y -> ( ph <-> ps ) ) $.
    $( Formula-building lemma for use with the Distinctor Reduction Theorem.
       Part of Theorem 9.4 of [Megill] p. 448 (p. 16 of preprint). $)
    dral1 $p |- ( A. x x = y -> ( A. x ph <-> A. y ps ) ) $=
      ( weq wal hbae biimpd alimd ax10o syld biimprd wi alequcoms impbid ) CDFC
      GZACGZBDGZQRBCGSQABCCDCHQABEIJBCDKLQSADGZRQBADCDDHQABEMJTRNDCADCKOLP $.
      $( [24-Nov-1994] $)
  $}

  ${
    dral2.1 $e |- ( A. x x = y -> ( ph <-> ps ) ) $.
    $( Formula-building lemma for use with the Distinctor Reduction Theorem.
       Part of Theorem 9.4 of [Megill] p. 448 (p. 16 of preprint). $)
    dral2 $p |- ( A. x x = y -> ( A. z ph <-> A. z ps ) ) $=
      ( weq wal hbae albid ) CDGCHABECDEIFJ $.
      $( [27-Feb-2005] $)
  $}

  ${
    drex1.1 $e |- ( A. x x = y -> ( ph <-> ps ) ) $.
    $( Formula-building lemma for use with the Distinctor Reduction Theorem.
       Part of Theorem 9.4 of [Megill] p. 448 (p. 16 of preprint). $)
    drex1 $p |- ( A. x x = y -> ( E. x ph <-> E. y ps ) ) $=
      ( weq wal wn wex notbid dral1 df-ex 3bitr4g ) CDFCGZAHZCGZHBHZDGZHACIBDIN
      PROQCDNABEJKJACLBDLM $.
      $( [27-Feb-2005] $)
  $}

  ${
    drex2.1 $e |- ( A. x x = y -> ( ph <-> ps ) ) $.
    $( Formula-building lemma for use with the Distinctor Reduction Theorem.
       Part of Theorem 9.4 of [Megill] p. 448 (p. 16 of preprint). $)
    drex2 $p |- ( A. x x = y -> ( E. z ph <-> E. z ps ) ) $=
      ( weq wal hbae exbid ) CDGCHABECDEIFJ $.
      $( [27-Feb-2005] $)
  $}

  ${
    exdistrf.1 $e |- ( -. A. x x = y -> ( ph -> A. y ph ) ) $.
    $( Distribution of existential quantifiers, with a bound-variable
       hypothesis saying that ` y ` is not free in ` ph ` , but ` x ` can be
       free in ` ph ` (and there is no distinct variable condition on ` x ` and
       ` y ` ).  (Contributed by Mario Carneiro, 20-Mar-2013.) $)
    exdistrf $p |- ( E. x E. y ( ph /\ ps ) -> E. x ( ph /\ E. y ps ) ) $=
      ( weq wal wa wex wi biidd drex1 drex2 hbe1 19.8a anim2i eximi sylbi hbnae
      19.9 syl6bir wn 19.40 19.9d anim1d syl5 eximd pm2.61i ) CDFCGZABHZDIZCIZA
      BDIZHZCIZJUIULUJCIZCIZUOUPUKCDCUJUJCDUIUJKLMUQUPUOUPCUJCNTUJUNCBUMABDOPQR
      UAUIUBZUKUNCCDCSUKADIZUMHURUNABDUCURUSAUMAURDCDDSEUDUEUFUGUH $.
      $( [20-Mar-2013] $)
  $}

  $( Closed theorem form of ~ a4im . $)
  a4imt $p |- ( A. x ( ( ps -> A. x ps ) /\ ( x = y -> ( ph -> ps ) ) ) ->
              ( A. x ph -> ps ) ) $=
    ( wal wi weq wa imim2 imim2d imp com23 al2imi ax9o syl6 ) BBCEZFZCDGZABFZFZ
    HZCEACERPFZCEBUAAUBCUARAPQTRAPFZFQSUCRBPAIJKLMBCDNO $.
    $( [15-Jan-2008] $)

  ${
    a4im.1 $e |- ( ps -> A. x ps ) $.
    a4im.2 $e |- ( x = y -> ( ph -> ps ) ) $.
    $( Specialization, using implicit substitition.  Compare Lemma 14 of
       [Tarski] p. 70.  The ~ a4im series of theorems requires that only one
       direction of the substitution hypothesis hold. $)
    a4im $p |- ( A. x ph -> ps ) $=
      ( wal weq wi syl6com alimi ax9o syl ) ACGCDHZBCGZIZCGBAPCNABOFEJKBCDLM $.
      $( [8-May-2008] $) $( [5-Aug-1993] $)
  $}

  ${
    a4ime.1 $e |- ( ph -> A. x ph ) $.
    a4ime.2 $e |- ( x = y -> ( ph -> ps ) ) $.
    $( Existential introduction, using implicit substitition.  Compare Lemma 14
       of [Tarski] p. 70. $)
    a4ime $p |- ( ph -> E. x ps ) $=
      ( wn wal wex hbn weq con3d a4im con2i df-ex sylibr ) ABGZCHZGBCIRAQAGCDAC
      EJCDKABFLMNBCOP $.
      $( [7-Aug-1994] $)
  $}

  ${
    a4imed.1 $e |- ( ch -> A. x ch ) $.
    a4imed.2 $e |- ( ch -> ( ph -> A. x ph ) ) $.
    a4imed.3 $e |- ( x = y -> ( ph -> ps ) ) $.
    $( Deduction version of ~ a4ime . $)
    a4imed $p |- ( ch -> ( ph -> E. x ps ) ) $=
      ( wex wa wal adantr imp 19.26 sylanbrc weq adantld a4ime ex ) CABDICAJZBD
      ETCDKZADKZTDKCUAAFLCAUBGMCADNODEPABCHQRS $.
      $( [5-Aug-1993] $)
  $}

  ${
    cbv1.1 $e |- ( ph -> ( ps -> A. y ps ) ) $.
    cbv1.2 $e |- ( ph -> ( ch -> A. x ch ) ) $.
    cbv1.3 $e |- ( ph -> ( x = y -> ( ps -> ch ) ) ) $.
    $( Rule used to change bound variables, using implicit substitition. $)
    cbv1 $p |- ( A. x A. y ph -> ( A. x ps -> A. y ch ) ) $=
      ( wal wi a4s al2imi ax-7 syl6 weq com23 syl6d ax9o a7s syld ) AEIZDIZBDIZ
      UCEIZCEIZUBUCBEIZDIUDUABUFDABUFJEFKLBDEMNAUDUEJEDADIZUCCEUGUCDEOZCDIZJZDI
      CABUJDABUHCUIAUHBCHPGQLCDERNLST $.
      $( [5-Aug-1993] $)
  $}


  ${
    cbv2.1 $e |- ( ph -> ( ps -> A. y ps ) ) $.
    cbv2.2 $e |- ( ph -> ( ch -> A. x ch ) ) $.
    cbv2.3 $e |- ( ph -> ( x = y -> ( ps <-> ch ) ) ) $.
    $( Rule used to change bound variables, using implicit substitition. $)
    cbv2 $p |- ( A. x A. y ph -> ( A. x ps <-> A. y ch ) ) $=
      ( wal weq wb wi bi1 syl6 cbv1 equcomi bi2 syl56 a7s impbid ) AEIDIBDIZCEI
      ZABCDEFGADEJZBCKZBCLHBCMNOAUBUALEDACBEDGFEDJUCAUDCBLEDPHBCQROST $.
      $( [5-Aug-1993] $)
  $}

  ${
    cbv3.1 $e |- ( ph -> A. y ph ) $.
    cbv3.2 $e |- ( ps -> A. x ps ) $.
    cbv3.3 $e |- ( x = y -> ( ph -> ps ) ) $.
    $( Rule used to change bound variables, using implicit substitition, that
       does not use ~ ax-12 . $)
    cbv3 $p |- ( A. x ph -> A. y ps ) $=
      ( wi wal imim2i a1i weq cbv1 id ax-gen mpg ) AAHZDIACIBDIHCQABCDAADIAEJBB
      CIHQFKCDLABHHQGKMQDANOP $.
      $( [5-Aug-1993] $)

    $( Rule used to change bound variables, using implicit substitition.  (The
       proof was shortened by Andrew Salmon, 25-May-2011.) $)
    cbv3ALT $p |- ( A. x ph -> A. y ps ) $=
      ( weq wal wi a1i cbv1 stdpc6 mpg ) DDHZDIACIBDIJCOABCDAADIJOEKBBCIJOFKCDH
      ABJJOGKLDMN $.
      $( [25-May-2011] $) $( [5-Aug-1993] $)
  $}

  ${
    cbval.1 $e |- ( ph -> A. y ph ) $.
    cbval.2 $e |- ( ps -> A. x ps ) $.
    cbval.3 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( Rule used to change bound variables, using implicit substitition.  (The
       proof was shortened by Andrew Salmon, 25-May-2011.) $)
    cbval $p |- ( A. x ph <-> A. y ps ) $=
      ( wal weq biimpd cbv3 wb equcoms biimprd impbii ) ACHBDHABCDEFCDIABGJKBAD
      CFEDCIABABLCDGMNKO $.
      $( [25-May-2011] $) $( [5-Aug-1993] $)
  $}

  ${
    cbvex.1 $e |- ( ph -> A. y ph ) $.
    cbvex.2 $e |- ( ps -> A. x ps ) $.
    cbvex.3 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( Rule used to change bound variables, using implicit substitition. $)
    cbvex $p |- ( E. x ph <-> E. y ps ) $=
      ( wex wn wal df-ex hbn weq notbid cbval xchbinx bitr4i ) ACHZBIZDJZIBDHRA
      IZCJTACKUASCDADELBCFLCDMABGNOPBDKQ $.
      $( [5-Aug-1993] $)
  $}

  ${
    chv2.1 $e |- ( ps -> A. x ps ) $.
    chv2.2 $e |- ( x = y -> ( ph <-> ps ) ) $.
    chv2.3 $e |- ph $.
    $( Implicit substitution of ` y ` for ` x ` into a theorem.  (Contributed
       by Raph Levien, 9-Jul-2003.) $)
    chvar $p |- ps $=
      ( weq biimpd a4im mpg ) ABCABCDECDHABFIJGK $.
      $( [9-Jul-2003] $)
  $}

  $( A variable introduction law for equality.  Lemma 15 of [Monk2] p. 109,
     however we do not require ` z ` to be distinct from ` x ` and ` y `
     (making the proof longer).  (The proof was shortened by Andrew Salmon,
     25-May-2011.) $)
  equvini $p |- ( x = y -> E. z ( x = z /\ z = y ) ) $=
    ( weq wal wa wex wi equcomi alimi a9e jctir a1d 19.29 syl6 eximi ax-mp a1ii
    wn hbnae anc2ri 19.29r wo ioran hban ax-12 ax-8 anc2li equcoms a4imed sylbi
    imp ecase3 ) CADZCEZCBDZCEZABDZACDZUPFZCGZHZUOURUSCEZUPCGZFZVAUOVEURUOVCVDU
    NUSCCAIZJCBKLMUSUPCNOUQURUSCGZUQFVAUQURVGUQURVGUNCGVGCAKUNUSCVFPQRUAUSUPCUB
    OUOUQUCSUOSZUQSZFZVBUOUQUDURUTVJCAVHVICCACTCBCTUEVHVIURURCEHABCUFULURUTHACU
    SURUPACBUGUHUIUJUKUM $.
    $( [25-May-2011] $) $( [5-Aug-1993] $)

  $( A variable elimination law for equality with no distinct variable
     requirements.  (Compare ~ equvini .) $)
  equveli $p |- ( A. z ( z = x <-> z = y ) -> x = y ) $=
    ( weq wb wal wi wa albiim equequ1 imbi12d a4s dral1 equid ax-4 syl6bi hbnae
    mpi wn pm2.61i equcomi syl adantld dral2 a1bi biimpri a1d hbequid a1i ax-12
    hban hbimd alrimi equtr ax-8 imim12d ax-gen 19.26 a4imt sylbir sylancl mpii
    imp ex adantrd sylbi ) CADZCBDZECFVGVHGZCFZVHVGGZCFZHZABDZVGVHCIVHCFZVMVNGV
    OVLVNVJVOVLBBDZBADZGZBFZVNVKVRCBVHVKVRECVHVHVPVGVQCBBJCBAJKLMVSVQVNVSVPVQBN
    VRBORBAUAUBPUCVOSZVJVNVLVGCFZVTVJVNGZGWAWBVTWAVJAADZVNGZCFZVNVIWDCACVGVIWDE
    CVGVGWCVHVNCAAJCABJKLUDWDVNCVNWDWCVNANZUEUFLPUGWASZVTWBWGVTHZVJWCVNWFWHWDWE
    GZCFZVGVIWDGGZCFZVJWDGZWHWICWGVTCCACQCBCQUKZWHWCVNCWNWCWCCFGWHACUHUIWGVTVNV
    NCFGABCUJVCULUMWKCVGWCVGVHVNCAAUNCABUOUPUQWJWLHWIWKHCFWMWIWKCURVIWDCAUSUTVA
    VBVDTVETVF $.
    $( [1-Mar-2013] $)

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Substitution (without distinct variables)
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $c [ $. $( Left bracket $)
  $c / $. $( Division. $)
  $c ] $.  $( Right bracket $)

  $( --- Start of patch to prevent connective overloading $)
  ${
    $v A $.
    wsbc.cA $f exp A $.
    $( Extend wff notation to include the proper substitution of a exp for a
       set.  Read this notation as "the proper substitution of exp ` A ` for
       set variable ` x ` in wff ` ph ` ."

       (The purpose of introducing ` wff [ A / x ] ph ` here is to allow us to
       express i.e.  "prove" the ~ wsb of predicate calculus in terms of the
       ~ wsbc of set theory, so that we don't "overload" its connectives with
       two syntax definitions.  This is done to prevent ambiguity that would
       complicate some Metamath parsers.  The exp variable ` A ` is introduced
       temporarily for the purpose of this definition but otherwise not used in
       predicate calculus.  See ~ df-sbc for more information on the set theory
       usage of ~ wsbc .) $)
    wsbc $a wff [ A / x ] ph $.
  $}

  $( Extend wff definition to include proper substitution (read "the wff that
     results when ` y ` is properly substituted for ` x ` in wff ` ph ` ").

     (Instead of introducing ~ wsb as an axiomatic statement, as was done in an
     older version of this database, we introduce it by "proving" a special
     case of set theory's more general ~ wsbc .  This lets us avoid overloading
     its connectives, thus preventing ambiguity that would complicate some
     Metamath parsers.  Note:  To see the proof steps of this syntax proof,
     type "show proof wsb /all" in the Metamath program.) $)
  wsb $p wff [ y / x ] ph $=
    ( cv wsbc ) ABCDE $.
    $( [24-Jan-2006] $)
  $( --- End of patch to prevent connective overloading $)

  $( --- Start of old code before overloading prevention patch. $)
  $(
  @( Extend wff definition to include proper substitution (read "the wff that
     results when ` y ` is properly substituted for ` x ` in wff ` ph ` ").

     After we introduce ~ cv and ~ wsbc in set theory, this syntax construction
     becomes redundant, since it can be derived with the proof
     "wph vx vy cv wsbc". @)
  wsb @a wff [ y / x ] ph @.
  $)
  $( --- End of old code before overloading prevention patch. $)

  $( Define proper substitution.  Remark 9.1 in [Megill] p. 447 (p. 15 of the
     preprint).  For our notation, we use ` [ y / x ] ph ` to mean "the wff
     that results when ` y ` is properly substituted for ` x ` in the wff
     ` ph ` ."  We can also use ` [ y / x ] ph ` in place of the "free for"
     side condition used in traditional predicate calculus; see, for example,
     ~ stdpc4 .

     Our notation was introduced in Haskell B. Curry's _Foundations of
     Mathematical Logic_ (1977), p. 316 and is frequently used in textbooks of
     lambda calculus and combinatory logic.  This notation improves the common
     but ambiguous notation, " ` ph ( y ) ` is the wff that results when ` y `
     is properly substituted for ` x ` in ` ph ( x ) ` ."  For example, if the
     original ` ph ( x ) ` is ` x = y ` , then ` ph ( y ) ` is ` y = y ` , from
     which we obtain that ` ph ( x ) ` is ` x = x ` .  So what exactly does
     ` ph ( x ) ` mean?  Curry's notation solves this problem.

     In most books, proper substitution has a somewhat complicated recursive
     definition with multiple cases based on the occurrences of free and bound
     variables in the wff.  Instead, we use a single formula that is exactly
     equivalent and gives us a direct definition.  We later prove that our
     definition has the properties we expect of proper substitution (see
     theorems ~ sbequ , ~ sbcom2 and ~ sbid2v ).

     Note that our definition is valid even when ` x ` and ` y ` are replaced
     with the same variable, as ~ sbid shows.  We achieve this by having ` x `
     free in the first conjunct and bound in the second.  We can also achieve
     this by using a dummy variable, as the alternate definition ~ dfsb7 shows
     (which some logicians may prefer because it doesn't mix free and bound
     variables).  Another version that mixes free and bound variables is
     ~ dfsb3 .  When ` x ` and ` y ` are distinct, we can express proper
     substitution with the simpler expressions of ~ sb5 and ~ sb6 .

     There are no restrictions on any of the variables, including what
     variables may occur in wff ` ph ` . $)
  df-sb $a |- ( [ y / x ] ph <->
              ( ( x = y -> ph ) /\ E. x ( x = y /\ ph ) ) ) $.

  ${
    sbimi.1 $e |- ( ph -> ps ) $.
    $( Infer substitution into antecedent and consequent of an implication. $)
    sbimi $p |- ( [ y / x ] ph -> [ y / x ] ps ) $=
      ( weq wi wa wex wsb imim2i anim2i eximi anim12i df-sb 3imtr4i ) CDFZAGZQA
      HZCIZHQBGZQBHZCIZHACDJBCDJRUATUCABQEKSUBCABQELMNACDOBCDOP $.
      $( [25-Jun-1998] $)
  $}

  ${
    sbbii.1 $e |- ( ph <-> ps ) $.
    $( Infer substitution into both sides of a logical equivalence. $)
    sbbii $p |- ( [ y / x ] ph <-> [ y / x ] ps ) $=
      ( wsb biimpi sbimi biimpri impbii ) ACDFBCDFABCDABEGHBACDABEIHJ $.
      $( [5-Aug-1993] $)
  $}

  $( Formula-building lemma for use with the Distinctor Reduction Theorem.
     Part of Theorem 9.4 of [Megill] p. 448 (p. 16 of preprint). $)
  drsb1 $p |- ( A. x x = y -> ( [ z / x ] ph <-> [ z / y ] ph ) ) $=
    ( weq wal wi wa wex wsb wb equequ1 a4s imbi1d anbi1d drex1 anbi12d 3bitr4g
    df-sb ) BCEZBFZBDEZAGZUBAHZBIZHCDEZAGZUFAHZCIZHABDJACDJUAUCUGUEUIUAUBUFATUB
    UFKBBCDLMZNUDUHBCUAUBUFAUJOPQABDSACDSR $.
    $( [5-Aug-1993] $)

  $( One direction of a simplified definition of substitution. $)
  sb1 $p |- ( [ y / x ] ph -> E. x ( x = y /\ ph ) ) $=
    ( wsb weq wi wa wex df-sb simprbi ) ABCDBCEZAFKAGBHABCIJ $.
    $( [5-Aug-1993] $)

  $( One direction of a simplified definition of substitution. $)
  sb2 $p |- ( A. x ( x = y -> ph ) -> [ y / x ] ph ) $=
    ( weq wi wal wa wex wsb ax-4 equs4 df-sb sylanbrc ) BCDZAEZBFONAGBHABCIOBJA
    BCKABCLM $.
    $( [5-Aug-1993] $)

  $( An equality theorem for substitution. $)
  sbequ1 $p |- ( x = y -> ( ph -> [ y / x ] ph ) ) $=
    ( weq wsb wa wi wex pm3.4 19.8a df-sb sylanbrc ex ) BCDZAABCEZNAFZNAGPBHONA
    IPBJABCKLM $.
    $( [5-Aug-1993] $)

  $( An equality theorem for substitution. $)
  sbequ2 $p |- ( x = y -> ( [ y / x ] ph -> ph ) ) $=
    ( wsb weq wi wa wex df-sb simpl com12 syl5bi ) ABCDBCEZAFZMAGBHZGZMAABCIPMA
    NOJKL $.
    $( [5-Aug-1993] $)

  $( One of the two equality axioms of standard predicate calculus, called
     substitutivity of equality.  (The other one is ~ stdpc6 .)  Translated to
     traditional notation, it can be
     read:  " ` x = y -> ( ph ( x , x ) -> ph ( x , y ) ) ` , provided that
     ` y ` is free for ` x ` in ` ph ( x , y ) ` ."  Axiom 7 of [Mendelson]
     p. 95. $)
  stdpc7 $p |- ( x = y -> ( [ x / y ] ph -> ph ) ) $=
    ( wsb wi sbequ2 equcoms ) ACBDAECBACBFG $.
    $( [15-Feb-2005] $)

  $( An equality theorem for substitution. $)
  sbequ12 $p |- ( x = y -> ( ph <-> [ y / x ] ph ) ) $=
    ( weq wsb sbequ1 sbequ2 impbid ) BCDAABCEABCFABCGH $.
    $( [5-Aug-1993] $)

  $( An equality theorem for substitution.  (The proof was shortened by Andrew
     Salmon, 21-Jun-2011.) $)
  sbequ12r $p |- ( x = y -> ( [ x / y ] ph <-> ph ) ) $=
    ( wsb wb weq sbequ12 bicomd equcoms ) ACBDZAECBCBFAJACBGHI $.
    $( [26-Jun-2011] $) $( [6-Oct-2004] $)

  $( An equality theorem for substitution. $)
  sbequ12a $p |- ( x = y -> ( [ y / x ] ph <-> [ x / y ] ph ) ) $=
    ( weq wsb sbequ12 wb equcoms bitr3d ) BCDAABCEACBEZABCFAJGCBACBFHI $.
    $( [5-Aug-1993] $)

  $( An identity theorem for substitution.  Remark 9.1 in [Megill] p. 447 (p.
     15 of the preprint). $)
  sbid $p |- ( [ x / x ] ph <-> ph ) $=
    ( wsb weq wb equid sbequ12 ax-mp bicomi ) AABBCZBBDAJEBFABBGHI $.
    $( [5-Aug-1993] $)

  $( The specialization axiom of standard predicate calculus.  It states that
     if a statement ` ph ` holds for all ` x ` , then it also holds for the
     specific case of ` y ` (properly) substituted for ` x ` .  Translated to
     traditional notation, it can be read:  " ` A. x ph ( x ) -> ph ( y ) ` ,
     provided that ` y ` is free for ` x ` in ` ph ( x ) ` ."  Axiom 4 of
     [Mendelson] p. 69.  See also ~ a4sbc and ~ ra4sbc . $)
  stdpc4 $p |- ( A. x ph -> [ y / x ] ph ) $=
    ( wal weq wi wsb ax-1 alimi sb2 syl ) ABDBCEZAFZBDABCGAMBALHIABCJK $.
    $( [5-Aug-1993] $)

  ${
    sbf.1 $e |- ( ph -> A. x ph ) $.
    $( Substitution for a variable not free in a wff does not affect it. $)
    sbf $p |- ( [ y / x ] ph <-> ph ) $=
      ( wsb weq wex wa sb1 19.41 sylib simprd wal stdpc4 syl impbii ) ABCEZAQBC
      FZBGZAQRAHBGSAHABCIRABDJKLAABMQDABCNOP $.
      $( [17-Oct-2004] $) $( [5-Aug-1993] $)
  $}

  $( Substitution has no effect on a bound variable. $)
  sbf2 $p |- ( [ y / x ] A. x ph <-> A. x ph ) $=
    ( wal hba1 sbf ) ABDBCABEF $.
    $( [1-Jul-2005] $)

  ${
    sb6x.1 $e |- ( ph -> A. x ph ) $.
    $( Equivalence involving substitution for a variable not free.  (The proof
       was shortened by Andrew Salmon, 12-Aug-2011.) $)
    sb6x $p |- ( [ y / x ] ph <-> A. x ( x = y -> ph ) ) $=
      ( cv wsbc wceq wi wal sbf biidd equsal bitr4i ) ABCEZFABENGZAHBIABCDJAABC
      DOAKLM $.
      $( [12-Aug-2011] $) $( [5-Aug-1993] $)
  $}

  ${
    hbs1f.1 $e |- ( ph -> A. x ph ) $.
    $( If ` x ` is not free in ` ph ` , it is not free in ` [ y / x ] ph ` .
       (The proof was shortened by Andrew Salmon, 25-May-2011.) $)
    hbs1f $p |- ( [ y / x ] ph -> A. x [ y / x ] ph ) $=
      ( wsb sbf hbxfrbi ) ABCEABABCDFDG $.
      $( [25-May-2011] $) $( [5-Aug-1993] $)
  $}

  $( Substitution does not change an identical variable specifier. $)
  sbequ5 $p |- ( [ w / z ] A. x x = y <-> A. x x = y ) $=
    ( weq wal hbae sbf ) ABEAFCDABCGH $.
    $( [21-Dec-2004] $) $( [5-Aug-1993] $)

  $( Substitution does not change a distinctor. $)
  sbequ6 $p |- ( [ w / z ] -. A. x x = y <-> -. A. x x = y ) $=
    ( weq wal wn hbnae sbf ) ABEAFGCDABCHI $.
    $( [14-May-2005] $) $( [5-Aug-1993] $)

  ${
    sbt.1 $e |- ph $.
    $( A substitution into a theorem remains true.  (See ~ chvar and ~ chvarv
       for versions using implicit substitition.)  (The proof was shortened by
       Andrew Salmon, 25-May-2011.) $)
    sbt $p |- [ y / x ] ph $=
      ( wsb hbth sbf mpbir ) ABCEADABCABDFGH $.
      $( [25-May-2011] $) $( [21-Jan-2004] $)
  $}

  $( Substitution applied to an atomic wff. $)
  equsb1 $p |- [ y / x ] x = y $=
    ( weq wi wsb sb2 id mpg ) ABCZIDIABEAIABFIGH $.
    $( [5-Aug-1993] $)

  $( Substitution applied to an atomic wff. $)
  equsb2 $p |- [ y / x ] y = x $=
    ( weq wi wsb sb2 equcomi mpg ) ABCBACZDIABEAIABFABGH $.
    $( [5-Aug-1993] $)

  ${
    sbied.1 $e |- ( ph -> A. x ph ) $.
    sbied.2 $e |- ( ph -> ( ch -> A. x ch ) ) $.
    sbied.3 $e |- ( ph -> ( x = y -> ( ps <-> ch ) ) ) $.
    $( Conversion of implicit substitution to explicit substitution (deduction
       version of ~ sbie ).  (The proof was shortened by Andrew Salmon,
       25-May-2011.) $)
    sbied $p |- ( ph -> ( [ y / x ] ps <-> ch ) ) $=
      ( wsb wex weq wa sb1 wb wi bi1 syl6 imp3a syld wal eximd syl5 19.9d com23
      bi2 alimd sb2 impbid ) ABDEIZCAUICDJZCUIDEKZBLZDJAUJBDEMAULCDFAUKBCAUKBCN
      ZBCOHBCPQRUAUBCADFGUCSACCDTZUIGAUNUKBOZDTUIACUODFAUKCBAUKUMCBOHBCUEQUDUFB
      DEUGQSUH $.
      $( [25-May-2011] $) $( [30-Jun-1994] $)
  $}

  ${
    sbie.1 $e |- ( ps -> A. x ps ) $.
    sbie.2 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( Conversion of implicit substitution to explicit substitution. $)
    sbie $p |- ( [ y / x ] ph <-> ps ) $=
      ( wi wsb wb id hbth wal a1i weq sbied ax-mp ) AAGZACDHBIAJZQABCDQCRKBBCLG
      QEMCDNABIGQFMOP $.
      $( [30-Jun-1994] $)
  $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                  Theorems using axiom ax-11
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( A property related to substitution that unlike ~ equs5 doesn't require a
     distinctor antecedent. $)
  equs5a $p |- ( E. x ( x = y /\ A. y ph ) -> A. x ( x = y -> ph ) ) $=
    ( weq wal wa wi hba1 ax-11 imp exlimi ) BCDZACEZFLAGZBEZBNBHLMOABCIJK $.
    $( [2-Feb-2007] $)

  $( A property related to substitution that unlike ~ equs5 doesn't require a
     distinctor antecedent. $)
  equs5e $p |- ( E. x ( x = y /\ ph ) -> A. x ( x = y -> E. y ph ) ) $=
    ( weq wa wex wn wi wal equs3 hbn1 ax-11 con3rr3 df-ex syl6ibr alrimi sylbi
    ) BCDZAEBFRAGZHZBIZGZRACFZHZBIABCJUBUDBTBKUBRSCIZGUCRUEUASBCLMACNOPQ $.
    $( [2-Feb-2007] $)

  $( A version of ~ sb4 that doesn't require a distinctor antecedent. $)
  sb4a $p |- ( [ y / x ] A. y ph -> A. x ( x = y -> ph ) ) $=
    ( wal wsb weq wa wex wi sb1 equs5a syl ) ACDZBCEBCFZMGBHNAIBDMBCJABCKL $.
    $( [2-Feb-2007] $)

  ${
    equs45f.1 $e |- ( ph -> A. y ph ) $.
    $( Two ways of expressing substitution when ` y ` is not free in
       ` ph ` . $)
    equs45f $p |- ( E. x ( x = y /\ ph ) <-> A. x ( x = y -> ph ) ) $=
      ( weq wa wex wi wal anim2i eximi equs5a syl equs4 impbii ) BCEZAFZBGZPAHB
      IZRPACIZFZBGSQUABATPDJKABCLMABCNO $.
      $( [25-Apr-2008] $)

    $( Equivalence for substitution when ` y ` is not free in ` ph ` . $)
    sb6f $p |- ( [ y / x ] ph <-> A. x ( x = y -> ph ) ) $=
      ( wsb weq wi wal sbimi sb4a syl sb2 impbii ) ABCEZBCFAGBHZNACHZBCEOAPBCDI
      ABCJKABCLM $.
      $( [30-Apr-2008] $)  $( [5-Aug-1993] $)

    $( Equivalence for substitution when ` y ` is not free in ` ph ` . $)
    sb5f $p |- ( [ y / x ] ph <-> E. x ( x = y /\ ph ) ) $=
      ( wsb weq wi wal wa wex sb6f equs45f bitr4i ) ABCEBCFZAGBHNAIBJABCDKABCDL
      M $.
      $( [18-May-2008] $)  $( [5-Aug-1993] $)
  $}

  $( One direction of a simplified definition of substitution that unlike ~ sb4
     doesn't require a distinctor antecedent. $)
  sb4e $p |- ( [ y / x ] ph -> A. x ( x = y -> E. y ph ) ) $=
    ( wsb weq wa wex wi wal sb1 equs5e syl ) ABCDBCEZAFBGMACGHBIABCJABCKL $.
    $( [2-Feb-2007] $)

  $( Special case of a bound-variable hypothesis builder for substitution. $)
  hbsb2a $p |- ( [ y / x ] A. y ph -> A. x [ y / x ] ph ) $=
    ( wal wsb weq wi sb4a sb2 a5i syl ) ACDBCEBCFAGZBDABCEZBDABCHLMBABCIJK $.
    $( [2-Feb-2007] $)

  $( Special case of a bound-variable hypothesis builder for substitution. $)
  hbsb2e $p |- ( [ y / x ] ph -> A. x [ y / x ] E. y ph ) $=
    ( wsb weq wex wi wal sb4e sb2 a5i syl ) ABCDBCEACFZGZBHMBCDZBHABCINOBMBCJKL
    $.
    $( [2-Feb-2007] $)

  ${
    hbsb3.1 $e |- ( ph -> A. y ph ) $.
    $( If ` y ` is not free in ` ph ` , ` x ` is not free in
       ` [ y / x ] ph ` . $)
    hbsb3 $p |- ( [ y / x ] ph -> A. x [ y / x ] ph ) $=
      ( wsb wal sbimi hbsb2a syl ) ABCEZACFZBCEJBFAKBCDGABCHI $.
      $( [5-Aug-1993] $)
  $}

$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
                  Predicate calculus with distinct variables
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Derive the axiom of distinct variables ax-16
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d x ps $.
    a4imv.1 $e |- ( x = y -> ( ph -> ps ) ) $.
    $( A version of ~ a4im with a distinct variable requirement instead of a
       bound variable hypothesis. $)
    a4imv $p |- ( A. x ph -> ps ) $=
      ( ax-17 a4im ) ABCDBCFEG $.
      $( [5-Aug-1993] $)
  $}

  ${
    $v f $.
    $( Define a temporary individual variable. $)
    aev.vf $f set f $.
    $d f u v $.  $d f u x y $.  $d u w $.
    $( A "distinctor elimination" lemma with no restrictions on variables in
       the consequent, proved without using ~ ax-16 .  (The proof was shortened
       by Andrew Salmon, 21-Jun-2011.) $)
    aev $p |- ( A. x x = y -> A. z w = v ) $=
      ( aev.vf vu weq wal hbae ax-8 a4imv alrimi equcomi alequcoms a5i alequcom
      syl6 3syl ) ABHZAIZDEHZCABCJUAFBHZFIZGEHZGIZUBUAUCFABFJTUCAFAFBKLMUDFGHZF
      IZEGHZEIUFUCUGFUGBFBFHZUGBGBGHUJGFHUGBGFKGFNRLOPUHUIEFGEJUGUIFEFEGKLMEGQS
      UEUBGDGDEKLSM $.
      $( [26-Jun-2011] $) $( [8-Nov-2006] $)
  $}

  ${
    $d x y $.  $d z ph $.
    $( Theorem showing that ~ ax-16 is redundant if ~ ax-17 is included in the
       axiom system.  The important part of the proof is provided by ~ aev .

       See ~ ax16ALT for an alternate proof that does not require ~ ax-10 or
       ~ ax-12 .

       This theorem should not be referenced in any proof.  Instead, use
       ~ ax-16 below so that theorems needing ~ ax-16 can be more easily
       identified. $)
    ax16 $p |- ( A. x x = y -> ( ph -> A. x ph ) ) $=
      ( vz weq wal wi aev ax-17 sbequ12 biimpcd alimd hbsb3 stdpc7 cbv3 syl6com
      wsb syl ) BCEBFBDEZDFZAABFZGBCDBDHATABDQZDFUAASUBDADIZSAUBABDJKLUBADBABDU
      CMUCADBNOPR $.
      $( [8-Nov-2006] $)
  $}

  ${
    $d x y $.
    $( Axiom of Distinct Variables.  The only axiom of predicate calculus
       requiring that variables be distinct (if we consider ~ ax-17 to be a
       metatheorem and not an axiom).  Axiom scheme C16' in [Megill] p. 448 (p.
       16 of the preprint).  It apparently does not otherwise appear in the
       literature but is easily proved from textbook predicate calculus by
       cases.  It is a somewhat bizarre axiom since the antecedent is always
       false in set theory (see ~ dtru ), but nonetheless it is technically
       necessary as you can see from its uses.

       This axiom is redundant if we include ~ ax-17 ; see theorem ~ ax16 .
       Alternately, ~ ax-17 becomes logically redundant in the presence of this
       axiom, but without ~ ax-17 we lose the more powerful metalogic that
       results from being able to express the concept of a set variable not
       occurring in a wff (as opposed to just two set variables being
       distinct).  We retain ~ ax-16 here to provide logical completeness for
       systems with the simpler metalogic that results from omitting ~ ax-17 ,
       which might be easier to study for some theoretical purposes. $)
    ax-16 $a |- ( A. x x = y -> ( ph -> A. x ph ) ) $.
  $}

  ${
    $d x z $.  $d y z $.
    $( Theorem to add distinct quantifier to atomic formula.  (This theorem
       demonstrates the induction basis for ~ ax-17 considered as a
       metatheorem.  Do not use it for later proofs - use ~ ax-17 instead, to
       avoid reference to the redundant axiom ~ ax-16 .) $)
    ax17eq $p |- ( x = y -> A. z x = y ) $=
      ( weq wal wi ax-12 ax-16 pm2.61ii ) CADCECBDCEABDZJCEFABCGJCAHJCBHI $.
      $( [5-Aug-1993] $)
  $}

  ${
    $d w z x $.  $d w y $.
    $( Quantifier introduction when one pair of variables is distinct. $)
    dveeq2 $p |- ( -. A. x x = y -> ( z = y -> A. x z = y ) ) $=
      ( vw weq ax-17 equequ2 dvelimfALT ) CDEZCBEZABDIAFJDFDBCGH $.
      $( [2-Jan-2002] $)

    $( Version of ~ dveeq2 using ~ ax-16 instead of ~ ax-17 . $)
    dveeq2ALT $p |- ( -. A. x x = y -> ( z = y -> A. x z = y ) ) $=
      ( vw weq ax17eq equequ2 dvelimfALT ) CDECBEABDCDAFCBDFDBCGH $.
      $( [29-Apr-2008] $)
  $}


  ${
    $d x z $.  $d y z $.
    dvelimfALT2.1 $e |- ( ph -> A. x ph ) $.
    dvelimfALT2.2 $e |- ( ps -> A. z ps ) $.
    dvelimfALT2.3 $e |- ( z = y -> ( ph <-> ps ) ) $.
    dvelimfALT2.4 $e |- ( -. A. x x = y -> ( z = y -> A. x z = y ) ) $.
    $( Proof of ~ dvelimf using ~ dveeq2 (shown as the last hypothesis) instead
       of ~ ax-12 .  This shows that ~ ax-12 could be replaced by ~ dveeq2 (the
       last hypothesis).  (Contributed by Andrew Salmon, 21-Jul-2011.) $)
    dvelimfALT2 $p |- ( -. A. x x = y -> ( ps -> A. x ps ) ) $=
      ( cv wceq wal wn wi ax-17 hbn1 a1i hbimd hbald equsal albii 3imtr3g ) CJD
      JZKZCLMZEJUCKZANZELZUHCLBBCLUEUGCEUEEOUEUFACUDCPIAACLNUEFQRSABEDGHTZUHBCU
      IUAUB $.
      $( [21-Jul-2011] $)
  $}

  ${
    $d z x $.
    $( A lemma for proving conditionless ZFC axioms. $)
    nd5 $p |- ( -. A. y y = x -> ( z = y -> A. x z = y ) ) $=
      ( cv wceq wal wi dveeq2 nalequcoms ) CDBDEZJAFGABABCHI $.
      $( [8-Jan-2002] $)
  $}

  ${
    $d x ch $.  $d x ph $.
    exlimdv.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Deduction from Theorem 19.23 of [Margaris] p. 90. $)
    exlimdv $p |- ( ph -> ( E. x ps -> ch ) ) $=
      ( ax-17 exlimd ) ABCDADFCDFEG $.
      $( [27-Apr-1994] $)
  $}

  ${
    $d x z $.  $d y z $.  $d z ph $.
    ax11v2.1 $e |- ( x = z -> ( ph -> A. x ( x = z -> ph ) ) ) $.
    $( Recovery of ~ ax11o from ~ ax11v without using ~ ax-11 .  The hypothesis
       is even weaker than ~ ax11v , with ` z ` both distinct from ` x ` _and_
       not occurring in ` ph ` .  Thus the hypothesis provides an alternate
       axiom that can be used in place of ~ ax11o . $)
    ax11v2 $p |- ( -. A. x x = y ->
                 ( x = y -> ( ph -> A. x ( x = y -> ph ) ) ) ) $=
      ( weq wal wn wex wi a9e wa wb equequ2 adantl dveeq2 imp hba1 imbi1d a4s
      albid syl imbi2d imbi12d mpbii ex exlimdv mpi ) BCFZBGHZDCFZDIUIAUIAJZBGZ
      JZJZDCKUJUKUODUJUKUOUJUKLZBDFZAUQAJZBGZJZJUOEUPUQUIUTUNUKUQUIMUJDCBNZOUPU
      SUMAUPUKBGZUSUMMUJUKVBBCDPQVBURULBUKBRUKURULMBUKUQUIAVASTUAUBUCUDUEUFUGUH
      $.
      $( [2-Feb-2007] $)
  $}

  ${
    $d x z $.  $d y z $.  $d z ph $.
    ax11a2.1 $e |- ( x = z -> ( A. z ph -> A. x ( x = z -> ph ) ) ) $.
    $( Derive ~ ax-11o from a hypothesis in the form of ~ ax-11 .  The
       hypothesis is even weaker than ~ ax-11 , with ` z ` both distinct from
       ` x ` and not occurring in ` ph ` .  Thus the hypothesis provides an
       alternate axiom that can be used in place of ~ ax11o .  As theorem
       ~ ax11 shows, the distinct variable conditions are optional.  An open
       problem is whether ~ ax11o can be derived from ~ ax-11 without relying
       on ~ ax-17 . $)
    ax11a2 $p |- ( -. A. x x = y ->
                 ( x = y -> ( ph -> A. x ( x = y -> ph ) ) ) ) $=
      ( wal weq wi ax-17 syl5 ax11v2 ) ABCDAADFBDGZLAHBFADIEJK $.
      $( [2-Feb-2007] $)
  $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Derive the obsolete axiom of variable substitution ax-11o
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d x z $.  $d y z $.  $d z ph $.
    $( Derivation of set.mm's original ~ ax-11o from the shorter ~ ax-11 that
       has replaced it.

       An open problem is whether this theorem can be proved without relying on
       ~ ax-16 or ~ ax-17 .

       Another open problem is whether this theorem can be proved without
       relying on ~ ax-12 (see note in ~ a12study ).

       Theorem ~ ax11 shows the reverse derivation of ~ ax-11 from ~ ax-11o .

       Normally, ~ ax11o should be used rather than ~ ax-11o , except by
       theorems specifically studying the latter's properties. $)
    ax11o $p |- ( -. A. x x = y ->
               ( x = y -> ( ph -> A. x ( x = y -> ph ) ) ) ) $=
      ( vz ax-11 ax11a2 ) ABCDABDEF $.
      $( [3-Feb-2007] $)
  $}

  $( Axiom ~ ax-11o ("o" for "old") was the original version of ~ ax-11 ,
     before it was discovered (in Jan. 2007) that the shorter ~ ax-11 could
     replace it.  It appears as Axiom scheme C15' in [Megill] p. 448 (p. 16 of
     the preprint).  It is based on Lemma 16 of [Tarski] p. 70 and Axiom C8 of
     [Monk2] p. 105, from which it can be proved by cases.  To understand this
     theorem more easily, think of " ` -. A. x x = y -> ` ..." as informally
     meaning "if ` x ` and ` y ` are distinct variables then..."  The
     antecedent becomes false if the same variable is substituted for ` x ` and
     ` y ` , ensuring the theorem is sound whenever this is the case.  In some
     later theorems, we call an antecedent of the form ` -. A. x x = y ` a
     "distinctor."

     This axiom is redundant, as shown by theorem ~ ax11o .

     Normally, ~ ax11o should be used rather than ~ ax-11o , except by theorems
     specifically studying the latter's properties. $)
  ax-11o $a |- ( -. A. x x = y ->
             ( x = y -> ( ph -> A. x ( x = y -> ph ) ) ) ) $.

  $( Rederivation of axiom ~ ax-11 from the orginal version, ~ ax-11o .  See
     theorem ~ ax11o for the derivation of ~ ax-11o from ~ ax-11 .

     This theorem should not be referenced in any proof.  Instead, use ~ ax-11
     above so that uses of ~ ax-11 can be more easily identified. $)
  ax11 $p |- ( x = y -> ( A. y ph -> A. x ( x = y -> ph ) ) ) $=
    ( weq wal wi biidd dral1 ax-1 alimi syl6bir a1d wn ax-4 ax-11o syl7 pm2.61i
    ) BCDZBEZRACEZRAFZBEZFZFSUCRSTABEUBAABCSAGHAUABARIJKLTASMRUBACNABCOPQ $.
    $( [22-Jan-2007] $)

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
     Theorems without distinct variables that use axiom ax-11o
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( A bidirectional version of ~ ax-11o . $)
  ax11b $p |- ( ( -. A. x x = y /\ x = y ) ->
              ( ph <-> A. x ( x = y -> ph ) ) ) $=
    ( weq wal wn wa wi ax-11o imp ax-4 com12 adantl impbid ) BCDZBEFZOGAOAHZBEZ
    POARHABCIJORAHPROAQBKLMN $.
    $( [30-Jun-2006] $)

  $( Lemma used in proofs of substitution properties. $)
  equs5 $p |- ( -. A. x x = y ->
             ( E. x ( x = y /\ ph ) -> A. x ( x = y -> ph ) ) ) $=
    ( weq wal wn wa wi hbnae hba1 ax11o imp3a exlimd ) BCDZBEFZNAGNAHZBEZBBCBIP
    BJONAQABCKLM $.
    $( [5-Aug-1993] $)

  $( One direction of a simplified definition of substitution when variables
     are distinct. $)
  sb3 $p |- ( -. A. x x = y -> ( E. x ( x = y /\ ph ) -> [ y / x ] ph ) ) $=
    ( weq wal wn wa wex wi wsb equs5 sb2 syl6 ) BCDZBEFNAGBHNAIBEABCJABCKABCLM
    $.
    $( [5-Aug-1993] $)

  $( One direction of a simplified definition of substitution when variables
     are distinct. $)
  sb4 $p |- ( -. A. x x = y -> ( [ y / x ] ph -> A. x ( x = y -> ph ) ) ) $=
    ( wsb weq wa wex wal wn wi sb1 equs5 syl5 ) ABCDBCEZAFBGNBHINAJBHABCKABCLM
    $.
    $( [5-Aug-1993] $)

  $( Simplified definition of substitution when variables are distinct. $)
  sb4b $p |- ( -. A. x x = y -> ( [ y / x ] ph <-> A. x ( x = y -> ph ) ) ) $=
    ( weq wal wn wsb wi sb4 sb2 impbid1 ) BCDZBEFABCGLAHBEABCIABCJK $.
    $( [27-May-1997] $)

  $( An alternate definition of proper substitution that, like ~ df-sb , mixes
     free and bound variables to avoid distinct variable requirements. $)
  dfsb2 $p |- ( [ y / x ] ph <->
              ( ( x = y /\ ph ) \/ A. x ( x = y -> ph ) ) ) $=
    ( wsb weq wa wi wal wo sbequ2 a4s ax-4 jctild orc wn sb4 olc pm2.61i sbequ1
    syl6 imp sb2 jaoi impbii ) ABCDZBCEZAFZUFAGBHZIZUFBHZUEUIGUJUEUGUIUJUEAUFUF
    UEAGBABCJKUFBLMUGUHNTUJOUEUHUIABCPUHUGQTRUGUEUHUFAUEABCSUAABCUBUCUD $.
    $( [17-Feb-2005] $)

  $( An alternate definition of proper substitution ~ df-sb that uses only
     primitive connectives (no defined terms) on the right-hand side. $)
  dfsb3 $p |- ( [ y / x ] ph <->
              ( ( x = y -> -. ph ) -> A. x ( x = y -> ph ) ) ) $=
    ( weq wa wi wal wo wn wsb df-or dfsb2 imnan imbi1i 3bitr4i ) BCDZAEZPAFBGZH
    QIZRFABCJPAIFZRFQRKABCLTSRPAMNO $.
    $( [6-Mar-2007] $)

  $( Bound-variable hypothesis builder for substitution. $)
  hbsb2 $p |- ( -. A. x x = y -> ( [ y / x ] ph -> A. x [ y / x ] ph ) ) $=
    ( weq wal wn wsb wi sb4 sb2 a5i syl6 ) BCDZBEFABCGZMAHZBENBEABCIONBABCJKL
    $.
    $( [5-Aug-1993] $)

  $( An equality theorem for substitution. $)
  sbequi $p |- ( x = y -> ( [ x / z ] ph -> [ y / z ] ph ) ) $=
    ( weq wal wsb wi wn wa wex hbsb2 stdpc7 sbequ1 sylan9 ex a4s adantr biimpd
    drsb1 equvini eximi syl 19.35 sylib hbnae 19.9d syl9 com23 sbequ2 alequcoms
    sylan9r syld pm2.61ii ) DBEZDFZDCEZDFZBCEZADBGZADCGZHZHUPIZUSURIZVBVCUSVDVB
    HVCUSJUTVADKZVDVAVCUTUTDFZUSVEADBLUSVBDKZVFVEHUSBDEZUQJZDKVGBCDUAVIVBDVHUTA
    UQVAABDMADCNZOUBUCUTVADUDUEOVAVDDDCDUFADCLUGUHPUIUPUSVBUPUSJUTAVAUPUTAHZUSU
    OVKDADBUJQRUSAABCGZUPVAABCNVLVAHBDVHBFVLVAABDCTSUKULUMPURUSVBURUSJUTAVAURUT
    ACBGZUSAURUTVMADCBTSABCMOURAVAHZUSUQVNDVJQRUMPUN $.
    $( [5-Aug-1993] $)

  $( An equality theorem for substitution.  Used in proof of Theorem 9.7 in
     [Megill] p. 449 (p. 16 of the preprint). $)
  sbequ $p |- ( x = y -> ( [ x / z ] ph <-> [ y / z ] ph ) ) $=
    ( weq wsb sbequi wi equcoms impbid ) BCEADBFZADCFZABCDGLKHCBACBDGIJ $.
    $( [5-Aug-1993] $)

  $( Formula-building lemma for use with the Distinctor Reduction Theorem.
     Part of Theorem 9.4 of [Megill] p. 448 (p. 16 of preprint). $)
  drsb2 $p |- ( A. x x = y -> ( [ x / z ] ph <-> [ y / z ] ph ) ) $=
    ( cv wceq wsbc wb sbequ a4s ) BEZCEZFADKGADLGHBABCDIJ $.
    $( [27-Feb-2005] $)

  $( Negation inside and outside of substitution are equivalent. $)
  sbn $p |- ( [ y / x ] -. ph <-> -. [ y / x ] ph ) $=
    ( wn wsb weq wal wi sbequ2 nsyld a4s sb4 wa wex sb1 equs3 sylib syl6 sylibr
    con2i pm2.61i sbequ1 con3rr3 sb2 notnot sbbii con3i df-sb sylanbrc impbii )
    ADZBCEZABCEZDZBCFZBGZULUNHZUOUQBUOULAUMUKBCIABCIJKUPDULUOUKHZBGZUNUKBCLUMUS
    UMUOAMBNUSDABCOABCPQTRUAUNURUOUKMBNZULUOAUMABCUBUCUNUOUKDZHBGZDUTVBUMVBVABC
    EUMVABCUDAVABCAUEUFSUGUKBCPSUKBCUHUIUJ $.
    $( [5-Aug-1993] $)

  $( Removal of implication from substitution. $)
  sbi1 $p |- ( [ y / x ] ( ph -> ps ) -> ( [ y / x ] ph -> [ y / x ] ps ) ) $=
    ( weq wal wi wsb sbequ2 syl5d sbequ1 syl6d a4s sb4 ax-2 al2imi syl6 pm2.61i
    wn sb2 ) CDEZCFZABGZCDHZACDHZBCDHZGGZUAUGCUAUDUEBUFUAUEAUDBACDIUCCDIJBCDKLM
    UBSZUEUAAGZCFZUDUFACDNUHUDUAUCGZCFZUJUFGUCCDNULUJUABGZCFUFUKUIUMCUAABOPBCDT
    QQJR $.
    $( [5-Aug-1993] $)

  $( Introduction of implication into substitution. $)
  sbi2 $p |- ( ( [ y / x ] ph -> [ y / x ] ps ) -> [ y / x ] ( ph -> ps ) ) $=
    ( wsb wi wn sbn pm2.21 sbimi sylbir ax-1 ja ) ACDEZBCDEABFZCDEZNGAGZCDEPACD
    HQOCDABIJKBOCDBALJM $.
    $( [5-Aug-1993] $)

  $( Implication inside and outside of substitution are equivalent. $)
  sbim $p |- ( [ y / x ] ( ph -> ps ) <-> ( [ y / x ] ph -> [ y / x ] ps ) ) $=
    ( wi wsb sbi1 sbi2 impbii ) ABECDFACDFBCDFEABCDGABCDHI $.
    $( [5-Aug-1993] $)

  $( Logical OR inside and outside of substitution are equivalent. $)
  sbor $p |- ( [ y / x ] ( ph \/ ps ) <-> ( [ y / x ] ph \/ [ y / x ] ps ) ) $=
    ( wn wi wsb wo sbim sbn imbi1i bitri df-or sbbii 3bitr4i ) AEZBFZCDGZACDGZE
    ZBCDGZFZABHZCDGSUAHRPCDGZUAFUBPBCDIUDTUAACDJKLUCQCDABMNSUAMO $.
    $( [29-Sep-2002] $)

  ${
    sbrim.1 $e |- ( ph -> A. x ph ) $.
    $( Substitution with a variable not free in antecedent affects only the
       consequent. $)
    sbrim $p |- ( [ y / x ] ( ph -> ps ) <-> ( ph -> [ y / x ] ps ) ) $=
      ( wi wsb sbim sbf imbi1i bitri ) ABFCDGACDGZBCDGZFAMFABCDHLAMACDEIJK $.
      $( [5-Aug-1993] $)
  $}

  ${
    sblim.1 $e |- ( ps -> A. x ps ) $.
    $( Substitution with a variable not free in consequent affects only the
       antecedent. $)
    sblim $p |- ( [ y / x ] ( ph -> ps ) <-> ( [ y / x ] ph -> ps ) ) $=
      ( wi wsb sbim sbf imbi2i bitri ) ABFCDGACDGZBCDGZFLBFABCDHMBLBCDEIJK $.
      $( [14-Nov-2013] $)
  $}

  $( Conjunction inside and outside of a substitution are equivalent. $)
  sban $p |- ( [ y / x ] ( ph /\ ps ) <-> ( [ y / x ] ph /\ [ y / x ] ps ) ) $=
    ( wn wi wsb wa sbn sbim imbi2i bitri xchbinx df-an sbbii 3bitr4i ) ABEZFZEZ
    CDGZACDGZBCDGZEZFZEABHZCDGUAUBHTRCDGZUDRCDIUFUAQCDGZFUDAQCDJUGUCUABCDIKLMUE
    SCDABNOUAUBNP $.
    $( [5-Aug-1993] $)

  $( Conjunction inside and outside of a substitution are equivalent. $)
  sb3an $p |- ( [ y / x ] ( ph /\ ps /\ ch ) <->
              ( [ y / x ] ph /\ [ y / x ] ps /\ [ y / x ] ch ) ) $=
    ( w3a wsb wa df-3an sbbii sban anbi1i bitr4i 3bitri ) ABCFZDEGABHZCHZDEGPDE
    GZCDEGZHZADEGZBDEGZSFZOQDEABCIJPCDEKTUAUBHZSHUCRUDSABDEKLUAUBSIMN $.
    $( [14-Dec-2006] $)

  $( Equivalence inside and outside of a substitution are equivalent. $)
  sbbi $p |- ( [ y / x ] ( ph <-> ps )
     <-> ( [ y / x ] ph <-> [ y / x ] ps ) ) $=
    ( wb wsb wi wa dfbi2 sbbii sbim anbi12i sban 3bitr4i bitri ) ABEZCDFABGZBAG
    ZHZCDFZACDFZBCDFZEZPSCDABIJQCDFZRCDFZHUAUBGZUBUAGZHTUCUDUFUEUGABCDKBACDKLQR
    CDMUAUBINO $.
    $( [5-Aug-1993] $)

  ${
    sblbis.1 $e |- ( [ y / x ] ph <-> ps ) $.
    $( Introduce left biconditional inside of a substitution. $)
    sblbis $p |- ( [ y / x ] ( ch <-> ph ) <-> ( [ y / x ] ch <-> ps ) ) $=
      ( wb wsb sbbi bibi2i bitri ) CAGDEHCDEHZADEHZGLBGCADEIMBLFJK $.
      $( [19-Aug-1993] $)
  $}

  ${
    sbrbis.1 $e |- ( [ y / x ] ph <-> ps ) $.
    $( Introduce right biconditional inside of a substitution. $)
    sbrbis $p |- ( [ y / x ] ( ph <-> ch ) <-> ( ps <-> [ y / x ] ch ) ) $=
      ( wb wsb sbbi bibi1i bitri ) ACGDEHADEHZCDEHZGBMGACDEILBMFJK $.
      $( [18-Aug-1993] $)
  $}

  ${
    sbrbif.1 $e |- ( ch -> A. x ch ) $.
    sbrbif.2 $e |- ( [ y / x ] ph <-> ps ) $.
    $( Introduce right biconditional inside of a substitution. $)
    sbrbif $p |- ( [ y / x ] ( ph <-> ch ) <-> ( ps <-> ch ) ) $=
      ( wb wsb sbrbis sbf bibi2i bitri ) ACHDEIBCDEIZHBCHABCDEGJNCBCDEFKLM $.
      $( [18-Aug-1993] $)
  $}

  $( A specialization theorem. $)
  a4sbe $p |- ( [ y / x ] ph -> E. x ph ) $=
    ( wsb wn wal wex stdpc4 sbn sylib con2i df-ex sylibr ) ABCDZAEZBFZEABGPNPOB
    CDNEOBCHABCIJKABLM $.
    $( [5-Aug-1993] $)

  $( Specialization of implication.  (The proof was shortened by Andrew Salmon,
     25-May-2011.) $)
  a4sbim $p |- ( A. x ( ph -> ps ) -> ( [ y / x ] ph -> [ y / x ] ps ) ) $=
    ( wi wal wsb stdpc4 sbi1 syl ) ABEZCFKCDGACDGBCDGEKCDHABCDIJ $.
    $( [25-May-2011] $) $( [5-Aug-1993] $)

  $( Specialization of biconditional. $)
  a4sbbi $p |- ( A. x ( ph <-> ps ) -> ( [ y / x ] ph <-> [ y / x ] ps ) ) $=
    ( wb wal wsb stdpc4 sbbi sylib ) ABEZCFKCDGACDGBCDGEKCDHABCDIJ $.
    $( [5-Aug-1993] $)

  ${
    sbbid.1 $e |- ( ph -> A. x ph ) $.
    sbbid.2 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Deduction substituting both sides of a biconditional. $)
    sbbid $p |- ( ph -> ( [ y / x ] ps <-> [ y / x ] ch ) ) $=
      ( wb wal wsb alrimi a4sbbi syl ) ABCHZDIBDEJCDEJHANDFGKBCDELM $.
      $( [5-Aug-1993] $)
  $}

  $( Elimination of equality from antecedent after substitution. $)
  sbequ8 $p |- ( [ y / x ] ph <-> [ y / x ] ( x = y -> ph ) ) $=
    ( wsb weq wi equsb1 a1bi sbim bitr4i ) ABCDZBCEZBCDZKFLAFBCDMKBCGHLABCIJ $.
    $( [5-Aug-1993] $)

  $( Substitution has no effect on a non-free variable. $)
  sbf3t $p |- ( A. x ( ph -> A. x ph ) -> ( [ y / x ] ph <-> ph ) ) $=
    ( wal wi wsb a4sbim sbf2 ax-4 sylbi syl6 stdpc4 imim2i a4s impbid ) AABDZEZ
    BDZABCFZARSPBCFZAAPBCGTPAABCHABIJKQASEBPSAABCLMNO $.
    $( [30-May-2009] $)

  ${
    hbsb4.1 $e |- ( ph -> A. z ph ) $.
    $( A variable not free remains so after substitution with a distinct
       variable. $)
    hbsb4 $p |- ( -. A. z z = y -> ( [ y / x ] ph -> A. z [ y / x ] ph ) ) $=
      ( weq wal wn wsb wi wb equequ1 a4s dral1 notbid hbsb2 alimi hbnae pm2.61i
      hban ax10o alequcoms sylbid hbae ax-4 sbequ2 sbequ1 al2imi syl5 syld 3syl
      syl9r wa a1d sb4 ax-12 imp a1i hbimd alimd sb2 a7s syl6 syl9 ex ) DBFZDGZ
      DCFZDGZHZABCIZVKDGZJZJVGVJBCFZBGZHZVMVGVIVOVHVNDBVFVHVNKDDBCLMNOVPVKVKBGZ
      VGVLABCPVQVLJBDVKBDUAUBULUCVGHZVJVMVOVRVJUMZVMJVOVMVSVOVODGVNDGZVMBCDUDVO
      VNDVNBUEQVTVKAVLVNVKAJDABCUFMAADGZVTVLEVNAVKDABCUGUHUIUJUKUNVPVKVNAJZBGZV
      SVLABCUOVSWCWBDGZBGVLVSWBWDBVRVJBDBBRDCBRTVSVNADVRVJDDBDRDCDRTVRVJVNVTJBC
      DUPUQAWAJVSEURUSUTWBVLDBWCVKDABCVAQVBVCVDSVES $.
      $( [5-Aug-1993] $)
  $}

  $( A variable not free remains so after substitution with a distinct variable
     (closed form of ~ hbsb4 ).  (The proof was shortened by Andrew Salmon,
     25-May-2011.) $)
  hbsb4t $p |- ( A. x A. z ( ph -> A. z ph ) ->
               ( -. A. z z = y -> ( [ y / x ] ph -> A. z [ y / x ] ph ) ) ) $=
    ( weq wal wn wsb wi hba1 hbsb4 a4sbim a4s ax-4 sbimi alimi a1i imim12d syl5
    a7s ) DCEDFGADFZBCHZUBDFZIZAUAIZDFBFABCHZUFDFZIZUABCDADJKUEUDUHIDBUEBFZDFZU
    FUBUCUGUIUFUBIDAUABCLMUCUGIUJUBUFDUAABCADNOPQRTS $.
    $( [25-May-2011] $) $( [7-Apr-2004] $)

  ${
    dvelimf.1 $e |- ( ph -> A. x ph ) $.
    dvelimf.2 $e |- ( ps -> A. z ps ) $.
    dvelimf.3 $e |- ( z = y -> ( ph <-> ps ) ) $.
    $( Version of ~ dvelim without any variable restrictions. $)
    dvelimf $p |- ( -. A. x x = y -> ( ps -> A. x ps ) ) $=
      ( weq wal wn wsb hbsb4 sbie albii 3imtr3g ) CDICJKAEDLZQCJBBCJAEDCFMABEDG
      HNZQBCROP $.
      $( [1-Oct-2002] $)
  $}

  ${
    dvelimdf.1 $e |- ( ph -> A. x ph ) $.
    dvelimdf.2 $e |- ( ph -> A. z ph ) $.
    dvelimdf.3 $e |- ( ph -> ( ps -> A. x ps ) ) $.
    dvelimdf.4 $e |- ( ph -> ( ch -> A. z ch ) ) $.
    dvelimdf.5 $e |- ( ph -> ( z = y -> ( ps <-> ch ) ) ) $.
    $( Deduction form of ~ dvelimf .  This version may be useful if we want to
       avoid ~ ax-17 and use ~ ax-16 instead. $)
    dvelimdf $p |- ( ph -> ( -. A. x x = y -> ( ch -> A. x ch ) ) ) $=
      ( weq wal wn wi wa wsb alrimi wb adantr 2alimi hbsb4t sbied albid 3imtr3d
      3syl imp ex ) ADELDMNZCCDMZOAUIPBFEQZUKDMZCUJAUIUKULOZAADMZFMBBDMOZDMFMUI
      UMOAUNFHGRAUOFDIUABFEDUBUFUGAUKCSUIABCFEHJKUCZTAULUJSUIAUKCDGUPUDTUEUH $.
      $( [7-Apr-2004] $)
  $}

  $( A composition law for substitution. $)
  sbco $p |- ( [ y / x ] [ x / y ] ph <-> [ y / x ] ph ) $=
    ( wsb wb weq equsb2 sbequ12 bicomd sbimi ax-mp sbbi mpbi ) ACBDZAEZBCDZNBCD
    ABCDECBFZBCDPBCGQOBCQANACBHIJKNABCLM $.
    $( [5-Aug-1993] $)

  ${
    sbid2.1 $e |- ( ph -> A. x ph ) $.
    $( An identity law for substitution. $)
    sbid2 $p |- ( [ y / x ] [ x / y ] ph <-> ph ) $=
      ( wsb sbco sbf bitri ) ACBEBCEABCEAABCFABCDGH $.
      $( [5-Aug-1993] $)
  $}

  $( An idempotent law for substitution.  (The proof was shortened by Andrew
     Salmon, 25-May-2011.) $)
  sbidm $p |- ( [ y / x ] [ y / x ] ph <-> [ y / x ] ph ) $=
    ( wsb wb weq equsb2 sbequ12r sbimi ax-mp sbbi mpbi ) ABCDZAEZBCDZMBCDMECBFZ
    BCDOBCGPNBCACBHIJMABCKL $.
    $( [25-May-2011] $) $( [30-Jun-1994] $)

  ${
    sbco2.1 $e |- ( ph -> A. z ph ) $.
    $( A composition law for substitution. $)
    sbco2 $p |- ( [ y / z ] [ z / x ] ph <-> [ y / x ] ph ) $=
      ( weq wal wsb wb sbid2 sbequ syl5bbr sbequ12 bitr3d a4s hbnae hbsb3 hbsb4
      wn wi a1i sbied bicomd pm2.61i ) BCFZBGZABDHZDCHZABCHZIZUEUJBUEAUHUIAUGDB
      HUEUHADBEJUGBCDKLZABCMNOUFSZUIUHULAUHBCBCBPUGDCBABDEQRUEAUHITULUKUAUBUCUD
      $.
      $( [30-Jun-1994] $)
  $}

  ${
    sbco2d.1 $e |- ( ph -> A. x ph ) $.
    sbco2d.2 $e |- ( ph -> A. z ph ) $.
    sbco2d.3 $e |- ( ph -> ( ps -> A. z ps ) ) $.
    $( A composition law for substitution. $)
    sbco2d $p |- ( ph -> ( [ y / z ] [ z / x ] ps <-> [ y / x ] ps ) ) $=
      ( wsb wi hbim1 sbco2 sbrim sbbii bitri 3bitr3i pm5.74ri ) ABCEIZEDIZBCDIZ
      ABJZCEIZEDIZUACDIASJZATJUACDEABEGHKLUCARJZEDIUDUBUEEDABCEFMNAREDGMOABCDFM
      PQ $.
      $( [5-Aug-1993] $)
  $}

  $( A composition law for substitution. $)
  sbco3 $p |- ( [ z / y ] [ y / x ] ph <-> [ z / x ] [ x / y ] ph ) $=
    ( weq wal wsb wb drsb1 sbequ12a alimi a4sbbi syl bitr3d wn sbco sbbii hbnae
    hbsb2 sbco2d syl5rbbr pm2.61i ) BCEZBFZABCGZCDGZACBGZBDGZHUDUEBDGZUFUHUEBCD
    IUDUEUGHZBFUIUHHUCUJBABCJKUEUGBDLMNUHUECBGZBDGUDOZUFUKUGBDACBPQULUECDBBCCRB
    CBRABCSTUAUB $.
    $( [5-Aug-1993] $)

  $( A commutativity law for substitution. $)
  sbcom $p |- ( [ y / z ] [ y / x ] ph <-> [ y / x ] [ y / z ] ph ) $=
    ( weq wal wsb wb wn wa hbae sbbid bitr3d hbnae hban albid sb4b sbequ12 a4s
    wi drsb1 adantr ax-12 imp alimi 19.21t 3syl adantrr alcom bi2.04 nalequcoms
    albii syl5bb adantrl imbi2d sylan9bbr adantl sylan9bb pm2.61ian ex pm2.61ii
    3bitr4d ) BCEZBFZDCEZDFZABCGZDCGZADCGZBCGZHZVDIZVFIZVKBDEBFZVLVMJZVKVNVKVOV
    NVGBCGVHVJVGBDCUAVNVGVIBCBDBKABDCUALMUBVNIZVOJZVEVCATZBFZTZDFZVCVEATZDFZTZB
    FZVHVJVQVEVRTZBFZDFZWAWEVPVLWHWAHVMVPVLJZWGVTDVPVLDBDDNZBCDNZOWIWIBFVEVEBFT
    ZBFWGVTHVPVLBBDBNZBCBNOWIWLBVPVLWLDCBUCUDUEVEVRBUFUGPUHVPVMWHWEHVLWHWFDFZBF
    VPVMJZWEWFDBUIWOWNWDBVPVMBWMDCBNZOWNVCWBTZDFZWOWDWFWQDVEVCAUJULWOWODFVCVCDF
    TZDFWRWDHVPVMDWJDCDNOWOWSDVPVMWSVMWSTDBBCDUCUKUDUEVCWBDUFUGUMPUMUNMVOVHWAHV
    PVMVHVEVGTZDFVLWAVGDCQVLWTVTDWKVLVGVSVEABCQUOPUPUQVOVJWEHVPVLVJVCVITZBFVMWE
    VIBCQVMXAWDBWPVMVIWCVCADCQUOPURUQVBUSUTVDVIVHVJVDAVGDCBCDKVCAVGHBABCRSLVCVI
    VJHBVIBCRSMVFVGVHVJVEVGVHHDVGDCRSVFAVIBCDCBKVEAVIHDADCRSLMVA $.
    $( [27-May-1997] $)

  ${
    sb5rf.1 $e |- ( ph -> A. y ph ) $.
    $( Reversed substitution.  (The proof was shortened by Andrew Salmon,
       25-May-2011.) $)
    sb5rf $p |- ( ph <-> E. y ( y = x /\ [ y / x ] ph ) ) $=
      ( weq wsb wa wex sbid2 sb1 sylbir stdpc7 imp exlimi impbii ) ACBEZABCFZGZ
      CHZAQCBFSACBDIQCBJKRACDPQAACBLMNO $.
      $( [25-May-2011] $) $( [3-Feb-2005] $)

    $( Reversed substitution.  (The proof was shortened by Andrew Salmon,
       25-May-2011.) $)
    sb6rf $p |- ( ph <-> A. y ( y = x -> [ y / x ] ph ) ) $=
      ( weq wsb wi wal sbequ1 equcoms com12 alrimi sb2 sbid2 sylib impbii ) ACB
      EZABCFZGZCHZASCDQARARGBCABCIJKLTRCBFARCBMACBDNOP $.
      $( [25-May-2011] $) $( [5-Aug-1993] $)
  $}

  ${
    sb8.1 $e |- ( ph -> A. y ph ) $.
    $( Substitution of variable in universal quantifier.  (The proof was
       shortened by Andrew Salmon, 25-May-2011.) $)
    sb8 $p |- ( A. x ph <-> A. y [ y / x ] ph ) $=
      ( wal wsb hbal stdpc4 alrimi hbsb3 stdpc7 cbv3 impbii ) ABEZABCFZCENOCACB
      DGABCHIOACBABCDJDACBKLM $.
      $( [25-May-2011] $) $( [5-Aug-1993] $)
  $}

  ${
    sb8e.1 $e |- ( ph -> A. y ph ) $.
    $( Substitution of variable in existential quantifier. $)
    sb8e $p |- ( E. x ph <-> E. y [ y / x ] ph ) $=
      ( wn wal wsb wex hbn sb8 sbn albii bitri notbii df-ex 3bitr4i ) AEZBFZEAB
      CGZEZCFZEABHSCHRUARQBCGZCFUAQBCACDIJUBTCABCKLMNABOSCOP $.
      $( [12-Aug-1993] $)
  $}

  $( Commutation of quantification and substitution variables. $)
  sb9i $p |- ( A. x [ x / y ] ph -> A. y [ y / x ] ph ) $=
    ( weq wal wi drsb1 drsb2 bitr3d dral1 biimprd wn hbsb2 al2imi hbnaes stdpc4
    wsb sbco sylib alimi a7s syl6 pm2.61i ) CBDCEZACBQZBEZABCQZCEZFUDUHUFUGUECB
    UDACCQUGUEACBCGACBCHIJKUDLZUFUECEZBEZUHUFUKFCBBUIUEUJBACBMNOUEUHCBUFUGCUFUE
    BCQUGUEBCPABCRSTUAUBUC $.
    $( [5-Aug-1993] $)

  $( Commutation of quantification and substitution variables. $)
  sb9 $p |- ( A. x [ x / y ] ph <-> A. y [ y / x ] ph ) $=
    ( wsb wal sb9i impbii ) ACBDBEABCDCEABCFACBFG $.
    $( [5-Aug-1993] $)

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Predicate calculus with distinct variables (cont.)
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d x y $.
    $( This is a version of ~ ax-11o when the variables are distinct.  Axiom
       (C8) of [Monk2] p. 105.  See theorem ~ ax11v2 for the rederivation of
       ~ ax-11o from this theorem. $)
    ax11v $p |- ( x = y -> ( ph -> A. x ( x = y -> ph ) ) ) $=
      ( weq wal wi ax-1 ax-16 syl5 a1d ax11o pm2.61i ) BCDZBEZMAMAFZBEZFZFNQMAO
      NPAMGOBCHIJABCKL $.
      $( [5-Aug-1993] $)

    $( Two equivalent ways of expressing the proper substitution of ` y ` for
       ` x ` in ` ph ` , when ` x ` and ` y ` are distinct.  Theorem 6.2 of
       [Quine] p. 40.  The proof does not involve ~ df-sb . $)
    sb56 $p |- ( E. x ( x = y /\ ph ) <-> A. x ( x = y -> ph ) ) $=
      ( weq wi wal hba1 ax11v ax-4 com12 impbid equsex ) ABCDZAEZBFZBCNBGMAOABC
      HOMANBIJKL $.
      $( [14-Apr-2008] $)

    $( Equivalence for substitution.  Compare Theorem 6.2 of [Quine] p. 40.
       Also proved as Lemmas 16 and 17 of [Tarski] p. 70. $)
    sb6 $p |- ( [ y / x ] ph <-> A. x ( x = y -> ph ) ) $=
      ( weq wi wa wex wal wsb sb56 anbi2i df-sb ax-4 pm4.71ri 3bitr4i ) BCDZAEZ
      PAFBGZFQQBHZFABCISRSQABCJKABCLSQQBMNO $.
      $( [14-Apr-2008] $) $( [18-Aug-1993] $)

    $( Equivalence for substitution.  Similar to Theorem 6.1 of [Quine]
       p. 40. $)
    sb5 $p |- ( [ y / x ] ph <-> E. x ( x = y /\ ph ) ) $=
      ( wsb weq wi wal wa wex sb6 sb56 bitr4i ) ABCDBCEZAFBGMAHBIABCJABCKL $.
      $( [14-Apr-2008] $) $( [18-Aug-1993] $)
  $}

  ${
    $d x y z $.  $d z ph $.
    ax16i.1 $e |- ( x = z -> ( ph <-> ps ) ) $.
    ax16i.2 $e |- ( ps -> A. x ps ) $.
    $( Inference with ~ ax-16 as its conclusion, that doesn't require ~ ax-10 ,
       ~ ax-11 , or ~ ax-12 for its proof.  The hypotheses may be eliminable
       without one or more of these axioms in special cases. $)
    ax16i $p |- ( A. x x = y -> ( ph -> A. x ph ) ) $=
      ( weq wal wi ax-17 ax-8 cbv3 a4imv equid1 mpi syl syl5com alimd mpcom
      alimi biimpcd biimprd syl6com ) CDHZCIZCEHZEIZAACIZJUFEDHZEIZUHUEUJCEUEEK
      ZUJCKCEDLMUKECHZEIZUHUEUKUNUJUEECECDLNUEUJUMEULUEDCHZUJUMUECCHUOCOCDCLPUJ
      DEHZUOUMJUJEEHZUPEOZEDELPDECLQRSTUMUGEUMUQUGURECELPZUAQQAUHBEIUIAUGBEAEKZ
      UGABFUBSBAECGUTUMUGBAJUSUGABFUCQMUDQ $.
      $( [20-May-2008] $)
  $}

  ${
    $d x y z $.  $d z ph $.
    $( Version of ~ ax16 that doesn't require ~ ax-10 or ~ ax-12 for its
       proof. $)
    ax16ALT $p |- ( A. x x = y -> ( ph -> A. x ph ) ) $=
      ( vz wsb sbequ12 ax-17 hbsb3 ax16i ) AABDEBCDABDFABDADGHI $.
      $( [17-May-2008] $)
  $}

  ${
    $d x ps $.
    a4v.1 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( Specialization, using implicit substitition. $)
    a4v $p |- ( A. x ph -> ps ) $=
      ( weq biimpd a4imv ) ABCDCDFABEGH $.
      $( [30-Aug-1993] $)
  $}

  ${
    $d x ph $.
    a4imev.1 $e |- ( x = y -> ( ph -> ps ) ) $.
    $( Distinct-variable version of ~ a4ime . $)
    a4imev $p |- ( ph -> E. x ps ) $=
      ( ax-17 a4ime ) ABCDACFEG $.
      $( [5-Aug-1993] $)
  $}

  ${
    $d x ps $.
    a4eiv.1 $e |- ( x = y -> ( ph <-> ps ) ) $.
    a4eiv.2 $e |- ps $.
    $( Inference from existential specialization, using implicit
       substitition. $)
    a4eiv $p |- E. x ph $=
      ( wex weq biimprd a4imev ax-mp ) BACGFBACDCDHABEIJK $.
      $( [19-Aug-1993] $)
  $}

  ${
    $d x z $.  $d y z $.
    $( A variable introduction law for equality.  Lemma 15 of [Monk2]
       p. 109. $)
    equvin $p |- ( x = y <-> E. z ( x = z /\ z = y ) ) $=
      ( weq wa wex equvini ax-17 equtr imp exlimi impbii ) ABDZACDZCBDZEZCFABCG
      PMCMCHNOMACBIJKL $.
      $( [5-Aug-1993] $)
  $}

  ${
    $d x y $.
    $( A generalization of axiom ~ ax-16 .  (The proof was shortened by Andrew
       Salmon, 25-May-2011.) $)
    a16g $p |- ( A. x x = y -> ( ph -> A. z ph ) ) $=
      ( weq wal aev ax-16 biidd dral1 biimprd sylsyld ) BCEBFDBEDFZAABFZADFZBCD
      DBGABCHMONAADBMAIJKL $.
      $( [25-May-2011] $) $( [5-Aug-1993] $)

    $( A generalization of axiom ~ ax-16 . $)
    a16gb $p |- ( A. x x = y -> ( ph <-> A. z ph ) ) $=
      ( weq wal a16g ax-4 impbid1 ) BCEBFAADFABCDGADHI $.
      $( [5-Aug-1993] $)
  $}

  ${
    $d x ph $.
    albidv.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Formula-building rule for universal quantifier (deduction rule). $)
    albidv $p |- ( ph -> ( A. x ps <-> A. x ch ) ) $=
      ( ax-17 albid ) ABCDADFEG $.
      $( [5-Aug-1993] $)

    $( Formula-building rule for existential quantifier (deduction rule). $)
    exbidv $p |- ( ph -> ( E. x ps <-> E. x ch ) ) $=
      ( ax-17 exbid ) ABCDADFEG $.
      $( [5-Aug-1993] $)
  $}

  ${
    $d x ph $.  $d y ph $.
    2albidv.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Formula-building rule for 2 existential quantifiers (deduction rule). $)
    2albidv $p |- ( ph -> ( A. x A. y ps <-> A. x A. y ch ) ) $=
      ( wal albidv ) ABEGCEGDABCEFHH $.
      $( [4-Mar-1997] $)

    $( Formula-building rule for 2 existential quantifiers (deduction rule). $)
    2exbidv $p |- ( ph -> ( E. x E. y ps <-> E. x E. y ch ) ) $=
      ( wex exbidv ) ABEGCEGDABCEFHH $.
      $( [1-May-1995] $)
  $}

  ${
    $d x ph $.  $d y ph $.  $d z ph $.
    3exbidv.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Formula-building rule for 3 existential quantifiers (deduction rule). $)
    3exbidv $p |- ( ph -> ( E. x E. y E. z ps <-> E. x E. y E. z ch ) ) $=
      ( wex exbidv 2exbidv ) ABFHCFHDEABCFGIJ $.
      $( [1-May-1995] $)
  $}

  ${
    $d x ph $.  $d y ph $.  $d z ph $.  $d w ph $.
    4exbidv.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Formula-building rule for 4 existential quantifiers (deduction rule). $)
    4exbidv $p |- ( ph ->
                     ( E. x E. y E. z E. w ps <-> E. x E. y E. z E. w ch ) ) $=
      ( wex 2exbidv ) ABGIFICGIFIDEABCFGHJJ $.
      $( [3-Aug-1995] $)
  $}

  ${
    $d x ph $.
    $( Special case of Theorem 19.9 of [Margaris] p. 89. $)
    19.9v $p |- ( E. x ph <-> ph ) $=
      ( ax-17 19.9 ) ABABCD $.
      $( [21-May-2007] $) $( [28-May-1995] $)
  $}

  ${
    $d x ph $.
    $( Special case of Theorem 19.21 of [Margaris] p. 90. _Notational
       convention_:  We sometimes suffix with "v" the label of a theorem
       eliminating a hypothesis such as ` ( ph -> A. x ph ) ` in ~ 19.21 via
       the use of distinct variable conditions combined with ~ ax-17 .
       Conversely, we sometimes suffix with "f" the label of a theorem
       introducing such a hypothesis to eliminate the need for the distinct
       variable condition; e.g. ~ euf derived from ~ df-eu .  The "f" stands
       for "not free in" which is less restrictive than "does not occur in." $)
    19.21v $p |- ( A. x ( ph -> ps ) <-> ( ph -> A. x ps ) ) $=
      ( ax-17 19.21 ) ABCACDE $.
      $( [5-Aug-1993] $)
  $}

  ${
    $d x ph $.
    alrimiv.1 $e |- ( ph -> ps ) $.
    $( Inference from Theorem 19.21 of [Margaris] p. 90. $)
    alrimiv $p |- ( ph -> A. x ps ) $=
      ( ax-17 alrimi ) ABCACEDF $.
      $( [5-Aug-1993] $)
  $}

  ${
    $d x ph $.  $d y ph $.
    alrimivv.1 $e |- ( ph -> ps ) $.
    $( Inference from Theorem 19.21 of [Margaris] p. 90. $)
    alrimivv $p |- ( ph -> A. x A. y ps ) $=
      ( wal alrimiv ) ABDFCABDEGG $.
      $( [31-Jul-1995] $)
  $}

  ${
    $d x ph $.  $d x ps $.
    alrimdv.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Deduction from Theorem 19.21 of [Margaris] p. 90. $)
    alrimdv $p |- ( ph -> ( ps -> A. x ch ) ) $=
      ( ax-17 alrimd ) ABCDADFBDFEG $.
      $( [10-Feb-1997] $)
  $}

  ${
    $d x ph $.  $d y ph $.
    $( Quantification of two variables over a formula in which they do not
       occur.  (Contributed by Alan Sare, 12-Apr-2011.) $)
    2ax17 $p |- ( ph -> A. x A. y ph ) $=
      ( id alrimivv ) AABCADE $.
      $( [12-Apr-2011] $)
  $}

  ${
    $d x ph $.
    alimdv.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Deduction from Theorem 19.20 of [Margaris] p. 90. $)
    alimdv $p |- ( ph -> ( A. x ps -> A. x ch ) ) $=
      ( ax-17 alimd ) ABCDADFEG $.
      $( [3-Apr-1994] $)

    $( Deduction from Theorem 19.22 of [Margaris] p. 90. $)
    eximdv $p |- ( ph -> ( E. x ps -> E. x ch ) ) $=
      ( ax-17 eximd ) ABCDADFEG $.
      $( [27-Apr-1994] $)
  $}

  ${
    $d x ph $.  $d y ph $.
    2alimdv.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Deduction from Theorem 19.22 of [Margaris] p. 90. $)
    2alimdv $p |- ( ph -> ( A. x A. y ps -> A. x A. y ch ) ) $=
      ( wal alimdv ) ABEGCEGDABCEFHH $.
      $( [27-Apr-2004] $)

    $( Deduction from Theorem 19.22 of [Margaris] p. 90. $)
    2eximdv $p |- ( ph -> ( E. x E. y ps -> E. x E. y ch ) ) $=
      ( wex eximdv ) ABEGCEGDABCEFHH $.
      $( [3-Aug-1995] $)
  $}

  ${
    $d x ps $.
    $( Special case of Theorem 19.23 of [Margaris] p. 90. $)
    19.23v $p |- ( A. x ( ph -> ps ) <-> ( E. x ph -> ps ) ) $=
      ( ax-17 19.23 ) ABCBCDE $.
      $( [28-Jun-1998] $)
  $}

  ${
    $d x ps $.  $d y ps $.
    $( Theorem 19.23 of [Margaris] p. 90 extended to two variables. $)
    19.23vv $p |- ( A. x A. y ( ph -> ps ) <-> ( E. x E. y ph -> ps ) ) $=
      ( wi wal wex 19.23v albii bitri ) ABEDFZCFADGZBEZCFLCGBEKMCABDHILBCHJ $.
      $( [10-Aug-2004] $)
  $}

  ${
    $d x ps $.
    exlimiv.1 $e |- ( ph -> ps ) $.
    $( Inference from Theorem 19.23 of [Margaris] p. 90.

       This inference, along with our many variants such as ~ rexlimdv , is
       used to implement a metatheorem called "Rule C" that is given in many
       logic textbooks.  See, for example, Rule C in [Mendelson] p. 81, Rule C
       in [Margaris] p. 40, or Rule C in Hirst and Hirst's _A Primer for Logic
       and Proof_ p. 59 (PDF p. 65) at
       ~ http://www.mathsci.appstate.edu/~~jlh/primer/hirst.pdf .

       In informal proofs, the statement "Let ` C ` be an element such that..."
       almost always means an implicit application of Rule C.

       In essence, Rule C states that if we can prove that some element ` x `
       exists satisfying a wff, i.e. ` E. x ph ( x ) ` where ` ph ( x ) ` has
       ` x ` free, then we can use ` ph ( C ) ` as a hypothesis for the proof
       where ` C ` is a new (ficticious) constant not appearing previously in
       the proof, nor in any axioms used, nor in the theorem to be proved.  The
       purpose of Rule C is to get rid of the existential quantifier.

       We cannot do this in Metamath directly.  Instead, we use the original
       ` ph ` (containing ` x ` ) as an antecedent for the main part of the
       proof.  We eventually arrive at ` ( ph -> ps ) ` where ` ps ` is the
       theorem to be proved and does not contain ` x ` .  Then we apply
       ~ exlimiv to arrive at ` ( E. x ph -> ps ) ` .  Finally, we separately
       prove ` E. x ph ` and detach it with modus ponens ~ ax-mp to arrive at
       the final theorem ` ps ` . $)
    exlimiv $p |- ( E. x ph -> ps ) $=
      ( ax-17 exlimi ) ABCBCEDF $.
      $( [25-Jul-2012] $) $( [5-Aug-1993] $)
  $}

  ${
    $d ph y $.  $d ps x $.
    $( Theorem *11.53 in [WhiteheadRussell] p. 164.  (Contributed by Andrew
       Salmon, 24-May-2011.) $)
    pm11.53 $p |- ( A. x A. y ( ph -> ps ) <-> ( E. x ph -> A. y ps ) ) $=
      ( wi wal wex 19.21v albii ax-17 hbal 19.23 bitri ) ABEDFZCFABDFZEZCFACGOE
      NPCABDHIAOCBCDBCJKLM $.
      $( [24-May-2011] $)
  $}

  ${
    $d x ps $.  $d y ps $.
    exlimivv.1 $e |- ( ph -> ps ) $.
    $( Inference from Theorem 19.23 of [Margaris] p. 90. $)
    exlimivv $p |- ( E. x E. y ph -> ps ) $=
      ( wex exlimiv ) ADFBCABDEGG $.
      $( [1-Aug-1995] $)
  $}

  ${
    $d x ch $.  $d x ph $.  $d y ch $.  $d y ph $.
    exlimdvv.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Deduction from Theorem 19.23 of [Margaris] p. 90. $)
    exlimdvv $p |- ( ph -> ( E. x E. y ps -> ch ) ) $=
      ( wex exlimdv ) ABEGCDABCEFHH $.
      $( [31-Jul-1995] $)
  $}

  ${
    $d x ps $.
    $( Theorem 19.27 of [Margaris] p. 90. $)
    19.27v $p |- ( A. x ( ph /\ ps ) <-> ( A. x ph /\ ps ) ) $=
      ( ax-17 19.27 ) ABCBCDE $.
      $( [3-Jun-2004] $)
  $}

  ${
    $d x ph $.
    $( Theorem 19.28 of [Margaris] p. 90. $)
    19.28v $p |- ( A. x ( ph /\ ps ) <-> ( ph /\ A. x ps ) ) $=
      ( ax-17 19.28 ) ABCACDE $.
      $( [25-Mar-2004] $)
  $}

  ${
    $d x ps $.
    $( Special case of Theorem 19.36 of [Margaris] p. 90. $)
    19.36v $p |- ( E. x ( ph -> ps ) <-> ( A. x ph -> ps ) ) $=
      ( ax-17 19.36 ) ABCBCDE $.
      $( [18-Aug-1993] $)
  $}

  ${
    $d x ps $.
    19.36aiv.1 $e |- E. x ( ph -> ps ) $.
    $( Inference from Theorem 19.36 of [Margaris] p. 90. $)
    19.36aiv $p |- ( A. x ph -> ps ) $=
      ( ax-17 19.36i ) ABCBCEDF $.
      $( [5-Aug-1993] $)
  $}

  ${
    $d x ps $.  $d y ph $.
    $( Special case of ~ 19.12 where its converse holds.  (Unnecessary distinct
       variable restrictions were removed by Andrew Salmon, 11-Jul-2011.) $)
    19.12vv $p |- ( E. x A. y ( ph -> ps ) <-> A. y E. x ( ph -> ps ) ) $=
      ( wal wex 19.21v exbii ax-17 hbal 19.36 19.36v albii 19.21 bitr2i 3bitri
      wi ) ABQZDEZCFABDEZQZCFACEZTQZRCFZDEZSUACABDGHATCBCDBCIJKUEUBBQZDEUCUDUFD
      ABCLMUBBDADCADIJNOP $.
      $( [11-Jul-2011] $) $( [18-Jul-2001] $)
  $}

  ${
    $d x ph $.
    $( Special case of Theorem 19.37 of [Margaris] p. 90. $)
    19.37v $p |- ( E. x ( ph -> ps ) <-> ( ph -> E. x ps ) ) $=
      ( ax-17 19.37 ) ABCACDE $.
      $( [5-Aug-1993] $)
  $}

  ${
    $d x ph $.
    19.37aiv.1 $e |- E. x ( ph -> ps ) $.
    $( Inference from Theorem 19.37 of [Margaris] p. 90. $)
    19.37aiv $p |- ( ph -> E. x ps ) $=
      ( wi wex 19.37v mpbi ) ABECFABCFEDABCGH $.
      $( [5-Aug-1993] $)
  $}

  ${
    $d x ps $.
    $( Special case of Theorem 19.41 of [Margaris] p. 90. $)
    19.41v $p |- ( E. x ( ph /\ ps ) <-> ( E. x ph /\ ps ) ) $=
      ( ax-17 19.41 ) ABCBCDE $.
      $( [5-Aug-1993] $)
  $}

  ${
    $d x ps $.  $d y ps $.
    $( Theorem 19.41 of [Margaris] p. 90 with 2 quantifiers. $)
    19.41vv $p |- ( E. x E. y ( ph /\ ps ) <-> ( E. x E. y ph /\ ps ) ) $=
      ( wa wex 19.41v exbii bitri ) ABEDFZCFADFZBEZCFKCFBEJLCABDGHKBCGI $.
      $( [30-Apr-1995] $)
  $}

  ${
    $d x ps $.  $d y ps $.  $d z ps $.
    $( Theorem 19.41 of [Margaris] p. 90 with 3 quantifiers. $)
    19.41vvv $p |- ( E. x E. y E. z ( ph /\ ps ) <->
                     ( E. x E. y E. z ph /\ ps ) ) $=
      ( wa wex 19.41vv exbii 19.41v bitri ) ABFEGDGZCGAEGDGZBFZCGMCGBFLNCABDEHI
      MBCJK $.
      $( [30-Apr-1995] $)
  $}

  ${
    $d w ps $.  $d x ps $.  $d y ps $.  $d z ps $.
    $( Theorem 19.41 of [Margaris] p. 90 with 4 quantifiers.  (Contributed by
       FL, 14-Jul-2007.) $)
    19.41vvvv $p |- ( E. w E. x E. y E. z ( ph /\ ps ) <->
                     ( E. w E. x E. y E. z ph /\ ps ) ) $=
      ( wa wex 19.41vvv exbii 19.41v bitri ) ABGEHDHCHZFHAEHDHCHZBGZFHNFHBGMOFA
      BCDEIJNBFKL $.
      $( [14-Jul-2007] $)
  $}

  ${
    $d x ph $.
    $( Special case of Theorem 19.42 of [Margaris] p. 90. $)
    19.42v $p |- ( E. x ( ph /\ ps ) <-> ( ph /\ E. x ps ) ) $=
      ( ax-17 19.42 ) ABCACDE $.
      $( [5-Aug-1993] $)
  $}

  ${
    $d y ph $.
    $( Distribution of existential quantifiers. $)
    exdistr $p |- ( E. x E. y ( ph /\ ps ) <-> E. x ( ph /\ E. y ps ) ) $=
      ( wa wex 19.42v exbii ) ABEDFABDFECABDGH $.
      $( [9-Mar-1995] $)
  $}

  ${
    $d x ph $.  $d y ph $.
    $( Theorem 19.42 of [Margaris] p. 90 with 2 quantifiers. $)
    19.42vv $p |- ( E. x E. y ( ph /\ ps ) <-> ( ph /\ E. x E. y ps ) ) $=
      ( wa wex exdistr 19.42v bitri ) ABEDFCFABDFZECFAJCFEABCDGAJCHI $.
      $( [16-Mar-1995] $)
  $}

  ${
    $d x ph $.  $d y ph $.  $d z ph $.
    $( Theorem 19.42 of [Margaris] p. 90 with 3 quantifiers. $)
    19.42vvv $p |- ( E. x E. y E. z ( ph /\ ps )
                       <-> ( ph /\ E. x E. y E. z ps ) ) $=
      ( wa wex 19.42vv exbii 19.42v bitri ) ABFEGDGZCGABEGDGZFZCGAMCGFLNCABDEHI
      AMCJK $.
      $( [21-Sep-2011] $)
  $}

  ${
    $d y ph $.  $d z ph $.
    $( Distribution of existential quantifiers. $)
    exdistr2 $p |- ( E. x E. y E. z ( ph /\ ps ) <->
                   E. x ( ph /\ E. y E. z ps ) ) $=
      ( wa wex 19.42vv exbii ) ABFEGDGABEGDGFCABDEHI $.
      $( [17-Mar-1995] $)
  $}

  ${
    $d y ph $.  $d z ph $.  $d z ps $.
    $( Distribution of existential quantifiers.  (The proof was shortened by
       Andrew Salmon, 25-May-2011.) $)
    3exdistr $p |- ( E. x E. y E. z ( ph /\ ps /\ ch ) <->
                E. x ( ph /\ E. y ( ps /\ E. z ch ) ) ) $=
      ( w3a wex wa 3anass 2exbii 19.42vv exdistr anbi2i 3bitri exbii ) ABCGZFHE
      HZABCFHIEHZIZDRABCIZIZFHEHAUAFHEHZITQUBEFABCJKAUAEFLUCSABCEFMNOP $.
      $( [25-May-2011] $) $( [9-Mar-1995] $)
  $}

  ${
    $d y ph $.  $d z ph $.  $d w ph $.  $d z ps $.  $d w ps $.  $d w ch $.
    $( Distribution of existential quantifiers. $)
    4exdistr $p |- ( E. x E. y E. z E. w ( ( ph /\ ps ) /\ ( ch /\ th ) ) <->
                E. x ( ph /\ E. y ( ps /\ E. z ( ch /\ E. w th ) ) ) ) $=
      ( wa wex anass exbii 19.42v anbi2i 3bitri bitri ) ABICDIZIZHJZGJZFJZABCDH
      JIZGJIZFJIZEUAAUCIZFJUDTUEFTABUBIZIZGJAUFGJZIUESUGGSABQIZIZHJZUGRUJHABQKL
      UKAUIHJZIABQHJZIZIUGAUIHMULUNABQHMNUNUFAUMUBBCDHMNNOPLAUFGMUHUCABUBGMNOLA
      UCFMPL $.
      $( [9-Mar-1995] $)
  $}

  ${
    $d y ph $.  $d x ps $.
    cbvalv.1 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( Rule used to change bound variables, using implicit substitition. $)
    cbvalv $p |- ( A. x ph <-> A. y ps ) $=
      ( ax-17 cbval ) ABCDADFBCFEG $.
      $( [5-Aug-1993] $)

    $( Rule used to change bound variables, using implicit substitition. $)
    cbvexv $p |- ( E. x ph <-> E. y ps ) $=
      ( ax-17 cbvex ) ABCDADFBCFEG $.
      $( [5-Aug-1993] $)
  $}

  ${
    $d y x $.  $d y z $.  $d w x $.  $d w z $.
    cbval2.1 $e |- ( ph -> A. z ph ) $.
    cbval2.2 $e |- ( ph -> A. w ph ) $.
    cbval2.3 $e |- ( ps -> A. x ps ) $.
    cbval2.4 $e |- ( ps -> A. y ps ) $.
    cbval2.5 $e |- ( ( x = z /\ y = w ) -> ( ph <-> ps ) ) $.
    $( Rule used to change bound variables, using implicit substitition. $)
    cbval2 $p |- ( A. x A. y ph <-> A. z A. w ps ) $=
      ( wal hbal weq wb wa ax-17 hban cbval 19.28v expcom pm5.32d 3bitr3i mpbir
      wi pm5.32 ) ADLZBFLZCEAEDGMBCFIMCENZUGUHOUEUIUGPZUIUHPZOUIAPZDLUIBPZFLUJU
      KULUMDFUIAFUIFQHRUIBDUIDQJRDFNZUIABUIUNABOKUAUBSUIADTUIBFTUCUIUGUHUFUDS
      $.
      $( [22-Dec-2003] $)

    $( Rule used to change bound variables, using implicit substitition. $)
    cbvex2 $p |- ( E. x E. y ph <-> E. z E. w ps ) $=
      ( wex hbex weq wb wa ax-17 hban cbvex 19.42v expcom pm5.32d 3bitr3i mpbir
      wi pm5.32 ) ADLZBFLZCEAEDGMBCFIMCENZUGUHOUEUIUGPZUIUHPZOUIAPZDLUIBPZFLUJU
      KULUMDFUIAFUIFQHRUIBDUIDQJRDFNZUIABUIUNABOKUAUBSUIADTUIBFTUCUIUGUHUFUDS
      $.
      $( [14-Sep-2003] $)
  $}

  ${
    $d z w ph $.  $d x y ps $.  $d x w $.  $d z y $.
    cbval2v.1 $e |- ( ( x = z /\ y = w ) -> ( ph <-> ps ) ) $.
    $( Rule used to change bound variables, using implicit substitition. $)
    cbval2v $p |- ( A. x A. y ph <-> A. z A. w ps ) $=
      ( ax-17 cbval2 ) ABCDEFAEHAFHBCHBDHGI $.
      $( [4-Feb-2005] $)

    $( Rule used to change bound variables, using implicit substitition. $)
    cbvex2v $p |- ( E. x E. y ph <-> E. z E. w ps ) $=
      ( ax-17 cbvex2 ) ABCDEFAEHAFHBCHBDHGI $.
      $( [26-Jul-1995] $)
  $}

  ${
    $d x ph $.  $d x ch $.
    cbvald.1 $e |- ( ph -> A. y ph ) $.
    cbvald.2 $e |- ( ph -> ( ps -> A. y ps ) ) $.
    cbvald.3 $e |- ( ph -> ( x = y -> ( ps <-> ch ) ) ) $.
    $( Deduction used to change bound variables, using implicit substitition,
       particularly useful in conjunction with ~ dvelim .  (The proof was
       shortened by Andrew Salmon, 25-May-2011.) $)
    cbvald $p |- ( ph -> ( A. x ps <-> A. y ch ) ) $=
      ( wal wb ax-17 hbal a17d cbv2 3syl ) AAEIZPDIBDICEIJFADEADKLABCDEGACDMHNO
      $.
      $( [25-May-2011] $) $( [2-Jan-2002] $)

    $( Deduction used to change bound variables, using implicit substitition,
       particularly useful in conjunction with ~ dvelim . $)
    cbvexd $p |- ( ph -> ( E. x ps <-> E. y ch ) ) $=
      ( wn wal wex hbnd weq wb notbi syl6ib cbvald notbid df-ex 3bitr4g ) ABIZD
      JZICIZEJZIBDKCEKAUBUDAUAUCDEFABEFGLADEMBCNUAUCNHBCOPQRBDSCEST $.
      $( [2-Jan-2002] $)
  $}

  ${
    $v f $.
    $v g $.
    $( Define temporary individual variables. $)
    cbvex4v.vf $f set f $.
    cbvex4v.vg $f set g $.
    $d w z ch $.  $d u v ph $.  $d x y ps $.  $d f g ps $.  $d f w $.
    $d g z $.  $d u v w x y z $.
    cbvex4v.1 $e |- ( ( x = v /\ y = u ) -> ( ph <-> ps ) ) $.
    cbvex4v.2 $e |- ( ( z = f /\ w = g ) -> ( ps <-> ch ) ) $.
    $( Rule used to change bound variables, using implicit substitition. $)
    cbvex4v $p |- ( E. x E. y E. z E. w ph <-> E. v E. u E. f E. g ch ) $=
      ( wex weq wa 2exbidv cbvex2v 2exbii bitri ) AGNFNZENDNBGNFNZINHNCKNJNZINH
      NUAUBDEHIDHOEIOPABFGLQRUBUCHIBCFGJKMRST $.
      $( [26-Jul-1995] $)
  $}

  ${
    eean.1 $e |- ( ph -> A. y ph ) $.
    eean.2 $e |- ( ps -> A. x ps ) $.
    $( Rearrange existential quantifiers. $)
    eean $p |- ( E. x E. y ( ph /\ ps ) <-> ( E. x ph /\ E. y ps ) ) $=
      ( wa wex 19.42 exbii hbex 19.41 bitri ) ABGDHZCHABDHZGZCHACHOGNPCABDEIJAO
      CBCDFKLM $.
      $( [27-Oct-2010] $)
  $}

  ${
    $d y ph $.  $d x ps $.
    $( Rearrange existential quantifiers. $)
    eeanv $p |- ( E. x E. y ( ph /\ ps ) <-> ( E. x ph /\ E. y ps ) ) $=
      ( ax-17 eean ) ABCDADEBCEF $.
      $( [26-Jul-1995] $)
  $}

  ${
    $d y ph $.  $d z ph $.  $d x z ps $.  $d x y ch $.
    $( Rearrange existential quantifiers.  (The proof was shortened by Andrew
       Salmon, 25-May-2011.) $)
    eeeanv $p |- ( E. x E. y E. z ( ph /\ ps /\ ch ) <->
                 ( E. x ph /\ E. y ps /\ E. z ch ) ) $=
      ( w3a wex wa df-3an 3exbii eeanv exbii anbi1i 19.41v 3bitr4i 3bitri ) ABC
      GZFHEHDHABIZCIZFHEHZDHSEHZCFHZIZDHZADHZBEHZUCGZRTDEFABCJKUAUDDSCEFLMUBDHZ
      UCIUFUGIZUCIUEUHUIUJUCABDELNUBUCDOUFUGUCJPQ $.
      $( [25-May-2011] $) $( [26-Jul-1995] $)
  $}

  ${
    $d z ph $.  $d w ph $.  $d x ps $.  $d y ps $.  $d y z $.  $d w x $.
    $( Rearrange existential quantifiers. $)
    ee4anv $p |- ( E. x E. y E. z E. w ( ph /\ ps ) <->
                  ( E. x E. y ph /\ E. z E. w ps ) ) $=
      ( wa wex excom exbii eeanv 2exbii 3bitri ) ABGFHZEHDHZCHNDHZEHZCHADHZBFHZ
      GZEHCHRCHSEHGOQCNDEIJPTCEABDFKLRSCEKM $.
      $( [31-Jul-1995] $)
  $}

  ${
    $d x ph $.
    nexdv.1 $e |- ( ph -> -. ps ) $.
    $( Deduction for generalization rule for negated wff. $)
    nexdv $p |- ( ph -> -. E. x ps ) $=
      ( ax-17 nexd ) ABCACEDF $.
      $( [5-Aug-1993] $)
  $}

  ${
    $d x ps $.
    chv.1 $e |- ( x = y -> ( ph <-> ps ) ) $.
    chv.2 $e |- ph $.
    $( Implicit substitution of ` y ` for ` x ` into a theorem. $)
    chvarv $p |- ps $=
      ( a4v mpg ) ABCABCDEGFH $.
      $( [20-Apr-1994] $)
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        More substitution theorems
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

$( The theorems in this section make use of the $d statement. $)

  ${
    $d y z $.  $d x y $.
    $( Lemma for ~ equsb3 .  (The proof was shortened by Andrew Salmon,
       14-Jun-2011.) $)
    equsb3lem $p |- ( [ x / y ] y = z <-> x = z ) $=
      ( cv wceq ax-17 equequ1 sbie ) BDCDZEADIEZBAJBFBACGH $.
      $( [14-Jun-2011] $) $( [4-Dec-2005] $)
  $}

  ${
    $d w y z $.  $d w x $.
    $( Substitution applied to an atomic wff.  (Contributed by Raph Levien and
       FL, 4-Dec-2005.) $)
    equsb3 $p |- ( [ x / y ] y = z <-> x = z ) $=
      ( vw weq wsb equsb3lem sbbii ax-17 sbco2 3bitr3i ) BCEZBDFZDAFDCEZDAFLBAF
      ACEMNDADBCGHLBADLDIJADCGK $.
      $( [4-Dec-2005] $)
  $}

  ${
    $d w y z $.  $d w x $.
    $( Substitution applied to an atomic membership wff.  (The proof was
       shortened by Andrew Salmon, 14-Jun-2011.) $)
    elsb3 $p |- ( [ x / y ] y e. z <-> x e. z ) $=
      ( vw wel wsb ax-17 elequ1 sbie sbbii sbco2 bitr3i wb weq sbimi ax-mp sbbi
      equsb1 mpbi sbf 3bitri ) BCEZBAFZDCEZDAFZACEZDAFZUFUCUDDBFZBAFUEUHUBBAUDU
      BDBUBDGDBCHIJUDDABUDBGKLUDUFMZDAFZUEUGMDANZDAFUJDARUKUIDADACHOPUDUFDAQSUF
      DAUFDGTUA $.
      $( [14-Jun-2011] $) $( [7-Nov-2006] $)
  $}

  ${
    $d w y z $.  $d w x $.
    $( Substitution applied to an atomic membership wff.  (Contributed by
       Rodolfo Medina, 3-Apr-2010.)  (The proof was shortened by Andrew Salmon,
       14-Jun-2011.) $)
    elsb4 $p |- ( [ x / y ] z e. y <-> z e. x ) $=
      ( vw wel wsb ax-17 elequ2 sbie sbbii sbco2 bitr3i wb weq sbimi ax-mp sbbi
      equsb1 mpbi sbf 3bitri ) CBEZBAFZCDEZDAFZCAEZDAFZUFUCUDDBFZBAFUEUHUBBAUDU
      BDBUBDGDBCHIJUDDABUDBGKLUDUFMZDAFZUEUGMDANZDAFUJDARUKUIDADACHOPUDUFDAQSUF
      DAUFDGTUA $.
      $( [14-Jun-2011] $) $( [3-Apr-2010] $)
  $}

  ${
    $d x y $.
    $( ` x ` is not free in ` [ y / x ] ph ` when ` x ` and ` y ` are
       distinct. $)
    hbs1 $p |- ( [ y / x ] ph -> A. x [ y / x ] ph ) $=
      ( weq wal wsb wi ax-16 hbsb2 pm2.61i ) BCDBEABCFZKBEGKBCHABCIJ $.
      $( [5-Aug-1993] $)
  $}

  ${
    $d y ph $.
    $( Two ways of expressing " ` x ` is (effectively) not free in ` ph ` ." $)
    sbhb $p |- ( ( ph -> A. x ph ) <-> A. y ( ph -> [ y / x ] ph ) ) $=
      ( wal wi wsb ax-17 sb8 imbi2i 19.21v bitr4i ) AABDZEAABCFZCDZEAMECDLNAABC
      ACGHIAMCJK $.
      $( [29-May-2009] $)
  $}

  ${
    $d x y z $.  $d y z ph $.
    $( Two ways of expressing " ` x ` is (effectively) not free in ` ph ` ."
       (Contributed by G&eacute;rard Lang, 14-Nov-2013.) $)
    sbhb2 $p |- ( A. x ( ph -> A. x ph )
           <-> A. y A. z ( [ y / x ] ph <-> [ z / x ] ph ) ) $=
      ( cv wsbc wb wal wi 2albiim sbhb albii alcom bitri ax-17 sb8 sblim 3bitri
      wa hbs1 anbi12i anidm 3bitr2ri ) ABCEZFZABDEZFZGDHCHUEUGIZDHCHZUGUEIZDHZC
      HZSAABHIZBHZUNSUNUEUGCDJUNUIUNULUNAUGIZBHZDHZUHCHZDHUIUNUODHZBHUQUMUSBABD
      KLUOBDMNUPURDUPUOBUDFZCHURUOBCUOCOPUTUHCAUGBCABDTQLNLUHDCMRUNAUEIZCHZBHVA
      BHZCHULUMVBBABCKLVABCMVCUKCVCVABUFFZDHUKVABDVADOPVDUJDAUEBDABCTQLNLRUAUNU
      BUC $.
      $( [14-Nov-2013] $)
  $}

  ${
    $d y z $.
    hbsb.1 $e |- ( ph -> A. z ph ) $.
    $( If ` z ` is not free in ` ph ` , it is not free in ` [ y / x ] ph ` when
       ` y ` and ` z ` are distinct. $)
    hbsb $p |- ( [ y / x ] ph -> A. z [ y / x ] ph ) $=
      ( weq wal wsb wi ax-16 hbsb4 pm2.61i ) DCFDGABCHZMDGIMDCJABCDEKL $.
      $( [12-Aug-1993] $)
  $}

  ${
    $d y z $.
    hbsbd.1 $e |- ( ph -> A. x ph ) $.
    hbsbd.2 $e |- ( ph -> A. z ph ) $.
    hbsbd.3 $e |- ( ph -> ( ps -> A. z ps ) ) $.
    $( Deduction version of ~ hbsb . $)
    hbsbd $p |- ( ph -> ( [ y / x ] ps -> A. z [ y / x ] ps ) ) $=
      ( cv wceq wal wsbc wi wn alrimi 2alimi hbsb4t 3syl ax-16 pm2.61d2 ) AEIDI
      ZJEKZBCUALZUCEKMZAAEKZCKBBEKMZEKCKUBNUDMAUECFGOAUFCEHPBCDEQRUCEDST $.
      $( [15-Feb-2013] $)
  $}

  ${
    $d x y z $.  $d w y $.
    $( Equivalence for double substitution. $)
    2sb5 $p |- ( [ z / x ] [ w / y ] ph <->
               E. x E. y ( ( x = z /\ y = w ) /\ ph ) ) $=
      ( wsb weq wa wex sb5 19.42v anass exbii anbi2i 3bitr4ri bitri ) ACEFZBDFB
      DGZQHZBIRCEGZHAHZCIZBIQBDJSUBBRTAHZHZCIRUCCIZHUBSRUCCKUAUDCRTALMQUERACEJN
      OMP $.
      $( [3-Feb-2005] $)

    $( Equivalence for double substitution. $)
    2sb6 $p |- ( [ z / x ] [ w / y ] ph <->
               A. x A. y ( ( x = z /\ y = w ) -> ph ) ) $=
      ( wsb weq wi wal wa sb6 19.21v impexp albii imbi2i 3bitr4ri bitri ) ACEFZ
      BDFBDGZRHZBISCEGZJAHZCIZBIRBDKTUCBSUAAHZHZCISUDCIZHUCTSUDCLUBUECSUAAMNRUF
      SACEKOPNQ $.
      $( [3-Feb-2005] $)
  $}

  ${
    $d x z $.  $d x w $.  $d y z $.
    $( Commutativity law for substitution.  Used in proof of Theorem 9.7 of
       [Megill] p. 449 (p. 16 of the preprint). $)
    sbcom2 $p |- ( [ w / z ] [ y / x ] ph <-> [ y / x ] [ w / z ] ph ) $=
      ( weq wal wsb wb wn wi albii 19.21v sb4b imbi2d albidv hbae sbequ12 sbbid
      a4s wa alcom bi2.04 bitri 3bitr3i a1i sylan9bbr sylan9bb 3bitr4d pm2.61ii
      ex bitr3d ) BCFZBGZDEFZDGZABCHZDEHZADEHZBCHZIZUNJZUPJZVAVBVCUAZUOUMAKZBGZ
      KZDGZUMUOAKZDGZKZBGZURUTVHVLIVDUMVIKZBGZDGVMDGZBGVHVLVMDBUBVNVGDVNUOVEKZB
      GVGVMVPBUMUOAUCLUOVEBMUDLVOVKBUMVIDMLUEUFVCURUOUQKZDGVBVHUQDENVBVQVGDVBUQ
      VFUOABCNOPUGVBUTUMUSKZBGVCVLUSBCNVCVRVKBVCUSVJUMADENOPUHUIUKUNUSURUTUNAUQ
      DEBCDQUMAUQIBABCRTSUMUSUTIBUSBCRTULUPUQURUTUOUQURIDUQDERTUPAUSBCDEBQUOAUS
      IDADERTSULUJ $.
      $( [27-May-1997] $)
  $}

  ${
    $d ph x y z $.  $d w x z $.
    $( Theorem *11.07 in [WhiteheadRussell] p. 159.  (Contributed by Andrew
       Salmon, 17-Jun-2011.) $)
    pm11.07 $p |- ( [ w / x ] [ y / z ] ph <-> [ y / x ] [ w / z ] ph ) $=
      ( cv wceq wa wex wsbc a9e pm3.2i 2th eeanv 3bitr4i anbi1i 19.41vv 2sb5 )
      BFZEFZGZDFZCFZGZHZAHDIBIZSUCGZUBTGZHZAHDIBIZADUCJBTJADTJBUCJUEDIBIZAHUIDI
      BIZAHUFUJUKULAUABIZUDDIZHZUGBIZUHDIZHZUKULUOURUMUNBEKDCKLUPUQBCKDEKLMUAUD
      BDNUGUHBDNOPUEABDQUIABDQOABDECRABDCERO $.
      $( [17-Jun-2011] $)
  $}

  ${
    $d x y $.
    $( Equivalence for substitution. $)
    sb6a $p |- ( [ y / x ] ph <-> A. x ( x = y -> [ x / y ] ph ) ) $=
      ( wsb weq wi wal sb6 wb sbequ12 equcoms pm5.74i albii bitri ) ABCDBCEZAFZ
      BGOACBDZFZBGABCHPRBOAQAQICBACBJKLMN $.
      $( [5-Aug-1993] $)
  $}

  ${
    $d x y $.  $d x w $.  $d y z $.  $d z w $.
    2sb5rf.1 $e |- ( ph -> A. z ph ) $.
    2sb5rf.2 $e |- ( ph -> A. w ph ) $.
    $( Reversed double substitution. $)
    2sb5rf $p |- ( ph <->
                E. z E. w ( ( z = x /\ w = y ) /\ [ z / x ] [ w / y ] ph ) ) $=
      ( weq wsb wex sb5rf 19.42v sbcom2 anbi2i anass bitri exbii hbsb 3bitr4ri
      wa ) ADBHZABDIZTZDJUAECHZTZACEIBDIZTZEJZDJABDFKUCUHDUAUDUBCEIZTZTZEJUAUJE
      JZTUHUCUAUJELUGUKEUGUEUITUKUFUIUEACEBDMNUAUDUIOPQUBULUAUBCEABDEGRKNSQP $.
      $( [3-Feb-2005] $)

    $( Reversed double substitution. $)
    2sb6rf $p |- ( ph <->
                A. z A. w ( ( z = x /\ w = y ) -> [ z / x ] [ w / y ] ph ) ) $=
      ( weq wsb wi wal wa sb6rf 19.21v sbcom2 imbi2i impexp bitri albii hbsb
      3bitr4ri ) ADBHZABDIZJZDKUBECHZLZACEIBDIZJZEKZDKABDFMUDUIDUBUEUCCEIZJZJZE
      KUBUKEKZJUIUDUBUKENUHULEUHUFUJJULUGUJUFACEBDOPUBUEUJQRSUCUMUBUCCEABDEGTMP
      UASR $.
      $( [3-Feb-2005] $)
  $}

  ${
    $d x z $.  $d y z $.  $d z ph $.
    $( An alternate definition of proper substitution ~ df-sb .  By introducing
       a dummy variable ` z ` in the definiens, we are able to eliminate any
       distinct variable restrictions among the variables ` x ` , ` y ` , and
       ` ph ` of the definiendum.  No distinct variable conflicts arise because
       ` z ` effectively insulates ` x ` from ` y ` .  To achieve this, we use
       a chain of two substitutions in the form of ~ sb5 , first ` z ` for
       ` x ` then ` y ` for ` z ` .  Compare Definition 2.1'' of [Quine] p. 17,
       which is obtained from this theorem by applying ~ df-clab .  Theorem
       ~ sb7f provides a version where ` ph ` and ` z ` don't have to be
       distinct. $)
    dfsb7 $p |- ( [ y / x ] ph <-> E. z ( z = y /\ E. x ( x = z /\ ph ) ) ) $=
      ( wsb weq wa wex sb5 sbbii ax-17 sbco2 3bitr3i ) ABDEZDCEBDFAGBHZDCEABCED
      CFOGDHNODCABDIJABCDADKLODCIM $.
      $( [28-Jan-2004] $)
  $}

  ${
    $d w x z $.  $d w y z $.  $d w ph $.
    sb7f.1 $e |- ( ph -> A. z ph ) $.
    $( This version of ~ dfsb7 does not require that ` ph ` and ` z ` be
       distinct.  This permits it to be used as a definition for substitution
       in a formalization that omits the logically redundant axiom ~ ax-17 i.e.
       that doesn't have the concept of a variable not occurring in a wff.
       ( ~ df-sb is also suitable, but its mixing of free and bound variables
       is distasteful to some logicians.)  (The proof was shortened by Andrew
       Salmon, 25-May-2011.) $)
    sb7f $p |- ( [ y / x ] ph <->
               E. z ( z = y /\ E. x ( x = z /\ ph ) ) ) $=
      ( wsb weq wa wex sb5 sbbii sbco2 3bitr3i ) ABDFZDCFBDGAHBIZDCFABCFDCGOHDI
      NODCABDJKABCDELODCJM $.
      $( [25-May-2011] $) $( [26-Jul-2006] $)
  $}

  ${
    $d x y $.
    sb10f.1 $e |- ( ph -> A. x ph ) $.
    $( Hao Wang's identity axiom P6 in Irving Copi, _Symbolic Logic_ (5th ed.,
       1979), p. 328.  In traditional predicate calculus, this is a sole axiom
       for identity from which the usual ones can be derived. $)
    sb10f $p |- ( [ y / z ] ph <-> E. x ( x = y /\ [ x / z ] ph ) ) $=
      ( weq wsb wa wex hbsb sbequ equsex bicomi ) BCFADBGZHBIADCGZNOBCADCBEJABC
      DKLM $.
      $( [9-May-2005] $)
  $}

  ${
    $d x ph $.
    $( An identity law for substitution.  Used in proof of Theorem 9.7 of
       [Megill] p. 449 (p. 16 of the preprint). $)
    sbid2v $p |- ( [ y / x ] [ x / y ] ph <-> ph ) $=
      ( ax-17 sbid2 ) ABCABDE $.
      $( [5-Aug-1993] $)
  $}

  ${
    $d x y $.  $d x ph $.
    $( Elimination of substitution. $)
    sbelx $p |- ( ph <-> E. x ( x = y /\ [ x / y ] ph ) ) $=
      ( wsb weq wa wex sbid2v sb5 bitr3i ) AACBDZBCDBCEKFBGABCHKBCIJ $.
      $( [5-Aug-1993] $)
  $}

  ${
    $( Note:  A more general case could also be proved with
       "$d x z $.  $d y w $.  $d x ph $.  $d y ph $.", but with more
       difficulty. $)
    $d x y z $.  $d w y $.  $d x y ph $.
    $( Elimination of double substitution. $)
    sbel2x $p |- ( ph <-> E. x E. y ( ( x = z /\ y = w ) /\
                     [ y / w ] [ x / z ] ph ) ) $=
      ( weq wsb wa wex sbelx anbi2i exbii exdistr 3bitr4i anass 2exbii bitr4i )
      ABDFZCEFZADBGZECGZHZHZCIBIZRSHUAHZCIBIRTHZBIRUBCIZHZBIAUDUFUHBTUGRTCEJKLA
      BDJRUBBCMNUEUCBCRSUAOPQ $.
      $( [5-Aug-1993] $)
  $}

  ${
    $d x y $.
    $( A theorem used in elimination of disjoint variable restriction on ` x `
       and ` y ` by replacing it with a distinctor ` -. A. x x = z ` . $)
    sbal1 $p |- ( -. A. x x = z ->
             ( [ z / y ] A. x ph <-> A. x [ z / y ] ph ) ) $=
      ( weq wal wn wsb wb wi sbequ12 a4s dral2 bitr3d a1d wa hba1 al2imi hbnaes
      syl6 hbsb4 ax-4 sbimi alimi adantl sb4 ax-7 dveeq2 alim sb2 sylan9 impbid
      syl9 ex pm2.61i ) CDEZCFZBDEBFGZABFZCDHZACDHZBFZIZJUQVCURUQUSUTVBUPUSUTIC
      USCDKLAVACDBUPAVAICACDKLMNOUQGZURVCVDURPUTVBURUTVBJVDURUTUTBFVBUSCDBABQUA
      UTVABUSACDABUBUCUDTUEVDVBUPAJZBFZCFZURUTVDVBVECFZBFZVGVBVIJCDBVDVAVHBACDU
      FRSVEBCUGTVGUTJBDCURCFVGUPUSJZCFUTURVFVJCURUPUPBFVFUSBDCUHUPABUIUMRUSCDUJ
      TSUKULUNUO $.
      $( [5-Aug-1993] $)
  $}

  ${
    $d x y $.  $d x z $.
    $( Move universal quantifier in and out of substitution. $)
    sbal $p |- ( [ z / y ] A. x ph <-> A. x [ z / y ] ph ) $=
      ( weq wal wsb wb a16gb sbimi sbequ5 sbbi 3imtr3i bitr3d sbal1 pm2.61i ) B
      DEBFZABFZCDGZACDGZBFZHQTSUAQCDGARHZCDGQTSHQUBCDABDBIJBDCDKARCDLMTBDBINABC
      DOP $.
      $( [5-Aug-1993] $)
  $}

  ${
    $d x y $.  $d x z $.
    $( Move existential quantifier in and out of substitution. $)
    sbex $p |- ( [ z / y ] E. x ph <-> E. x [ z / y ] ph ) $=
      ( wn wal wsb wex sbn sbal albii bitri xchbinx df-ex sbbii 3bitr4i ) AEZBF
      ZEZCDGZACDGZEZBFZEABHZCDGUABHTRCDGZUCRCDIUEQCDGZBFUCQBCDJUFUBBACDIKLMUDSC
      DABNOUABNP $.
      $( [27-Sep-2003] $)
  $}

  ${
    $d x z $.  $d y z $.
    sbalv.1 $e |- ( [ y / x ] ph <-> ps ) $.
    $( Quantify with new variable inside substitution. $)
    sbalv $p |- ( [ y / x ] A. z ph <-> A. z ps ) $=
      ( wal wsb sbal albii bitri ) AEGCDHACDHZEGBEGAECDILBEFJK $.
      $( [18-Aug-1993] $)
  $}

  ${
    $d x y $.  $d y ph $.
    $( An equivalent expression for existence. $)
    exsb $p |- ( E. x ph <-> E. y A. x ( x = y -> ph ) ) $=
      ( wex wsb weq wi wal ax-17 sb8e sb6 exbii bitri ) ABDABCEZCDBCFAGBHZCDABC
      ACIJNOCABCKLM $.
      $( [2-Feb-2005] $)
  $}

  ${
    $d x y z $.  $d y w $.  $d z w ph $.
    $( An equivalent expression for double existence. $)
    2exsb $p |- ( E. x E. y ph <->
                  E. z E. w A. x A. y ( ( x = z /\ y = w ) -> ph ) ) $=
      ( wex weq wi wal exsb exbii excom bitri impexp albii 19.21v bitr2i 3bitri
      wa ) ACFZBFZCEGZAHZCIZBFZEFZBDGZUBSAHZCIZBIZDFZEFUJEFDFUAUDEFZBFUFTULBACE
      JKUDBELMUEUKEUEUGUDHZBIZDFUKUDBDJUNUJDUMUIBUIUGUCHZCIUMUHUOCUGUBANOUGUCCP
      QOKMKUJEDLR $.
      $( [2-Feb-2005] $)
  $}

  ${
    $d z ps $.
    dvelim.1 $e |- ( ph -> A. x ph ) $.
    dvelim.2 $e |- ( z = y -> ( ph <-> ps ) ) $.
    $( This theorem can be used to eliminate a distinct variable restriction on
       ` x ` and ` z ` and replace it with the "distinctor" ` -. A. x x = y `
       as an antecedent. ` ph ` normally has ` z ` free and can be read
       ` ph ( z ) ` , and ` ps ` substitutes ` y ` for ` z ` and can be read
       ` ph ( y ) ` .  We don't require that ` x ` and ` y ` be distinct: if
       they aren't, the distinctor will become false (in multiple-element
       domains of discourse) and "protect" the consequent.

       To obtain a closed-theorem form of this inference, prefix the hypotheses
       with ` A. x A. z ` , conjoin them, and apply ~ dvelimdf .

       Other variants of this theorem are ~ dvelimf (with no distinct variable
       restrictions), ~ dvelimfALT (that avoids ~ ax-11 ), and ~ dvelimALT
       (that avoids ~ ax-10 ). $)
    dvelim $p |- ( -. A. x x = y -> ( ps -> A. x ps ) ) $=
      ( ax-17 dvelimf ) ABCDEFBEHGI $.
      $( [23-Nov-1994] $)
  $}

  ${
    $d z ps $.  $d x z $.  $d y z $.
    dvelimALT.1 $e |- ( ph -> A. x ph ) $.
    dvelimALT.2 $e |- ( z = y -> ( ph <-> ps ) ) $.
    $( Version of ~ dvelim that doesn't use ~ ax-10 .  (See ~ dvelimfALT for a
       version that doesn't use ~ ax-11 .) $)
    dvelimALT $p |- ( -. A. x x = y -> ( ps -> A. x ps ) ) $=
      ( weq wal wn wi ax-17 hba1 ax16ALT a1i hbimd a1d wa hbn hban ax-12 imp ex
      pm2.61i hbald equsal albii 3imtr3g ) CDHZCIZJZEDHZAKZEIZUNCIBBCIUKUMCEUKE
      LCEHZCIZUKUMUMCIKZKUPUQUKUPULACUOCMZULCENAACIKZUPFOPQUPJZUKUQUTUKRZULACUT
      UKCUPCURSUJCUICMSTUTUKULULCIKEDCUAUBUSVAFOPUCUDUEABEDBELGUFZUNBCVBUGUH $.
      $( [17-May-2008] $)
  $}

  ${
    $d w z x $.  $d w y $.
    $( Quantifier introduction when one pair of variables is distinct. $)
    dveeq1 $p |- ( -. A. x x = y -> ( y = z -> A. x y = z ) ) $=
      ( vw weq ax-17 equequ1 dvelim ) DCEZBCEABDIAFDBCGH $.
      $( [2-Jan-2002] $)

    $( Version of ~ dveeq1 using ~ ax-16 instead of ~ ax-17 . $)
    dveeq1ALT $p |- ( -. A. x x = y -> ( y = z -> A. x y = z ) ) $=
      ( vw weq ax17eq equequ1 dvelimfALT ) DCEBCEABDDCAFBCDFDBCGH $.
      $( [29-Apr-2008] $)
  $}

  ${
    $d w z x $.  $d w y $.
    $( Quantifier introduction when one pair of variables is distinct. $)
    dveel1 $p |- ( -. A. x x = y -> ( y e. z -> A. x y e. z ) ) $=
      ( vw wel ax-17 elequ1 dvelimfALT ) DCEZBCEZABDIAFJDFDBCGH $.
      $( [2-Jan-2002] $)
  $}

  ${
    $d w z x $.  $d w y $.
    $( Quantifier introduction when one pair of variables is distinct. $)
    dveel2 $p |- ( -. A. x x = y -> ( z e. y -> A. x z e. y ) ) $=
      ( vw wel ax-17 elequ2 dvelimfALT ) CDEZCBEZABDIAFJDFDBCGH $.
      $( [2-Jan-2002] $)
  $}

  ${
    $d z y $.  $d z x $.
    $( Move quantifier in and out of substitution. $)
    sbal2 $p |- ( -. A. x x = y ->
             ( [ z / y ] A. x ph <-> A. x [ z / y ] ph ) ) $=
      ( weq wal wn wi wsb alcom hbnae dveeq1 alimi hbnaes 19.21t albid syl5rbbr
      wb syl sb6 albii 3bitr4g ) BCEBFGZCDEZABFZHZCFZUDAHZCFZBFZUECDIACDIZBFUJU
      HBFZCFUCUGUHCBJUCULUFCBCCKUCUDUDBFHZBFZULUFRUNBCBUCUMBBCDLMNUDABOSPQUECDT
      UKUIBACDTUAUB $.
      $( [2-Jan-2002] $)
  $}

  ${
    $d w y $.  $d w z $.  $d w x $.  $( ` w ` is dummy. $)
    $( Axiom ~ ax-15 is redundant if we assume ~ ax-17 .  Remark 9.6 in
       [Megill] p. 448 (p. 16 of the preprint), regarding axiom scheme C14'.

       Note that ` w ` is a dummy variable introduced in the proof.  On the web
       page, it is implicitly assumed to be distinct from all other variables.
       (This is made explicit in the database file set.mm).  Its purpose is to
       satisfy the distinct variable requirements of ~ dveel2 and ~ ax-17 .  By
       the end of the proof it has vanished, and the final theorem has no
       distinct variable requirements.

       This theorem should not be referenced in any proof.  Instead, use
       ~ ax-15 below so that theorems needing ~ ax-15 can be more easily
       identified. $)
    ax15 $p |- ( -. A. z z = x -> ( -. A. z z = y ->
              ( x e. y -> A. z x e. y ) ) ) $=
      ( vw weq wal wn wi hbn1 dveel2 hbim1 ax-17 elequ1 imbi2d dvelimfALT 19.21
      wel syl6ib pm2.86d ) CAECFGZCBEZCFGZABQZUCCFZTUBUCHZUECFUBUDHUBDBQZHUECAD
      UBUFCUACIZCBDJKUEDLDAEUFUCUBDABMNOUBUCCUGPRS $.
      $( [29-Jun-1995] $)
  $}

  $( Axiom of Quantifier Introduction.  One of the equality and substitution
     axioms for a non-logical predicate in our predicate calculus with
     equality.  Axiom scheme C14' in [Megill] p. 448 (p. 16 of the preprint).
     It is redundant if we include ~ ax-17 ; see theorem ~ ax15 .  Alternately,
     ~ ax-17 becomes unnecessary in principle with this axiom, but we lose the
     more powerful metalogic afforded by ~ ax-17 .  We retain ~ ax-15 here to
     provide completeness for systems with the simpler metalogic that results
     from omitting ~ ax-17 , which might be easier to study for some
     theoretical purposes. $)
  ax-15 $a |- ( -. A. z z = x -> ( -. A. z z = y ->
              ( x e. y -> A. z x e. y ) ) ) $.

  ${
    $d x z $.  $d y z $.
    $( Theorem to add distinct quantifier to atomic formula.  This theorem
       demonstrates the induction basis for ~ ax-17 considered as a
       metatheorem.) $)
    ax17el $p |- ( x e. y -> A. z x e. y ) $=
      ( weq wal wel wi ax-15 ax-16 pm2.61ii ) CADCECBDCEABFZKCEGABCHKCAIKCBIJ
      $.
      $( [5-Aug-1993] $)
  $}

  ${
    $d w z x $.  $d w y $.
    $( Version of ~ dveel2 using ~ ax-16 instead of ~ ax-17 . $)
    dveel2ALT $p |- ( -. A. x x = y -> ( z e. y -> A. x z e. y ) ) $=
      ( vw wel ax17el elequ2 dvelimfALT ) CDECBEABDCDAFCBDFDBCGH $.
      $( [10-May-2008] $)
  $}

  ${
    $d x u v $.  $d y u v $.  $d z u v $.  $d w u v $.
    $( Basis step for constructing a substitution instance of ~ ax-11o without
       using ~ ax-11o .  Atomic formula for equality predicate. $)
    ax11eq $p |- ( -. A. x x = y ->
               ( x = y -> ( z = w -> A. x ( x = y -> z = w ) ) ) ) $=
      ( vu vv weq wal wn wi wa 19.26 a1i wb equequ1 equequ2 a4s imbi2d imbi12d
      exp32 equid ax-gen sylan9bb hba1 albid adantr mpbii sylbir ad2antll ax-12
      impcom adantrr equtrr alimi syl6 sylbid dral2 ad2antrr mpbid imp biimprcd
      adantll adantlr ad2antlr wex a9e ax-1 alrimiv adantl im2anan9 syl exlimdv
      dveeq2 sylibr mpi a1d 4cases ) ACGZAHZADGZAHZABGZAHIZWBCDGZWBWDJZAHZJZJZJ
      ZVSWAKVRVTKZAHZWIVRVTALWKWCWBWGWKWCWBKZKAAGZWBWMJZAHZJZWGWOWMWNAWMWBAUAMU
      BMWKWPWGNWLWKWMWDWOWFWJWMWDNAVRWMCAGZVTWDACAOADCPZUCQZWKWNWEAWJAUDWKWMWDW
      BWSRUESUFUGTUHVSWAIZKZWCWBWGXAWLKVTWBVTJZAHZJZWGWTWLXDVSWTWLKZVTBDGZXCWBV
      TXFNWTWCABDOUIXEXFXFAHZXCWTWCXFXGJZWBWCWTXHBDAUJUKULXFXBABDAUMUNUOUPVBVSX
      DWGNWTWLVSVTWDXCWFVRVTWDNAACDOQZXBWEACAVSVTWDWBXIRUQSURUSTVSIZWAKZWCWBWGX
      KWLKWQWBWQJZAHZJZWGXJWLXNWAXJWLKZWQCBGZXMWBWQXPNXJWCABCPZUIXOXPXPAHZXMXJW
      CXPXRJZWBXJWCXSCBAUJUTULXPXLAWBWQXPXQVAUNUOUPVCWAXNWGNXJWLWAWQWDXMWFVTWQW
      DNAWRQZXLWEADAWAWQWDWBXTRUQSVDUSTXJWTKZWHWCYAWGWBYAEDGZEVEWGEDVFYAYBWGEYA
      FCGZFVEYBWGJZFCVFYAYCYDFYAYCYBWGYAYCYBKZKZFEGZWBYGJZAHZJWGYGYHAYGWBVGVHYF
      YGWDYIWFYEYGWDNZYAYCYGCEGYBWDFCEOEDCPUCZVIYFYEAHZYIWFNYFYCAHZYBAHZKZYLYAY
      EYOXJYCYMWTYBYNACFVMADEVMVJUTYCYBALVNYLYHWEAYEAUDYLYGWDWBYEYJAYKQRUEVKSUG
      TVLVOVLVOVPVPVQ $.
      $( [22-Jan-2007] $)
  $}

  ${
    $d x u v $.  $d y u v $.  $d z u v $.  $d w u v $.
    $( Basis step for constructing a substitution instance of ~ ax-11o without
       using ~ ax-11o .  Atomic formula for membership predicate. $)
    ax11el $p |- ( -. A. x x = y ->
               ( x = y -> ( z e. w -> A. x ( x = y -> z e. w ) ) ) ) $=
      ( vv vu weq wal wn wel wi wa wb elequ1 elequ2 adantl imbi2d imbi12d exp32
      a4s 19.26 bitrd ax-17 dvelimfALT biimprcd alimi syl6 adantr sylan9bb hba1
      sylbid albid mpbid sylbir ad2antll ax-15 impcom adantrr adantll dral2 imp
      ad2antrr adantlr ad2antlr wex a9e ax-1 alrimiv dveeq2 im2anan9 sylibr syl
      mpbii exlimdv mpi a1d 4cases ) ACGZAHZADGZAHZABGZAHIZWBCDJZWBWDKZAHZKZKZK
      ZVSWALVRVTLZAHZWIVRVTAUAWKWCWBWGWKWCWBLZLAAJZWBWMKZAHZKZWGWLWPWKWLWMBBJZW
      OWBWMWQMWCWBWMBAJWQABANABBOUBZPWCWQWOKWBWCWQWQAHWOEEJZWQABEWSAUCWQEUCEBGW
      SBEJWQEBENEBBOUBUDWQWNAWBWMWQWRUEUFUGUHUKPWKWPWGMWLWKWMWDWOWFWJWMWDMAVRWM
      CAJZVTWDACANADCOZUITZWKWNWEAWJAUJWKWMWDWBXBQULRUHUMSUNVSWAIZLZWCWBWGXDWLL
      ADJZWBXEKZAHZKZWGXCWLXHVSXCWLLZXEBDJZXGWBXEXJMXCWCABDNZUOXIXJXJAHZXGXCWCX
      JXLKZWBWCXCXMBDAUPUQURXJXFAWBXEXJXKUEUFUGUKUSVSXHWGMXCWLVSXEWDXGWFVRXEWDM
      AACDNTZXFWEACAVSXEWDWBXNQUTRVBUMSVSIZWALZWCWBWGXPWLLWTWBWTKZAHZKZWGXOWLXS
      WAXOWLLZWTCBJZXRWBWTYAMXOWCABCOZUOXTYAYAAHZXRXOWCYAYCKZWBXOWCYDCBAUPVAURY
      AXQAWBWTYAYBUEUFUGUKVCWAXSWGMXOWLWAWTWDXRWFVTWTWDMAXATZXQWEADAWAWTWDWBYEQ
      UTRVDUMSXOXCLZWHWCYFWGWBYFFDGZFVEWGFDVFYFYGWGFYFECGZEVEYGWGKZECVFYFYHYIEY
      FYHYGWGYFYHYGLZLZEFJZWBYLKZAHZKWGYLYMAYLWBVGVHYKYLWDYNWFYJYLWDMZYFYHYLCFJ
      YGWDECFNFDCOUIZPYKYJAHZYNWFMYKYHAHZYGAHZLZYQYFYJYTXOYHYRXCYGYSACEVIADFVIV
      JVAYHYGAUAVKYQYMWEAYJAUJYQYLWDWBYJYOAYPTQULVLRVMSVNVOVNVOVPVPVQ $.
      $( [22-Jan-2007] $)
  $}

  ${
    ax11f.1 $e |- ( ph -> A. x ph ) $.
    $( Basis step for constructing a substitution instance of ~ ax-11o without
       using ~ ax-11o .  We can start with any formula ` ph ` in which ` x ` is
       not free. $)
    ax11f $p |- ( -. A. x x = y ->
               ( x = y -> ( ph -> A. x ( x = y -> ph ) ) ) ) $=
      ( weq wal wn wi ax-1 alrimi a1ii ) BCEZBFGLALAHZBFHAMBDALIJK $.
      $( [21-Jan-2007] $)
  $}

  ${
    ax11indn.1 $e |- ( -. A. x x = y ->
               ( x = y -> ( ph -> A. x ( x = y -> ph ) ) ) ) $.
    $( Induction step for constructing a substitution instance of ~ ax-11o
       without using ~ ax-11o .  Negation case. $)
    ax11indn $p |- ( -. A. x x = y ->
               ( x = y -> ( -. ph -> A. x ( x = y -> -. ph ) ) ) ) $=
      ( weq wal wn wi wex 19.8a exanali hbn1 con3 syl6 com23 alrimd syl5bi syl5
      wa exp3a ) BCEZBFGZUAAGZUAUCHZBFZUAUCSZUFBIZUBUEUFBJUGUAAHZBFZGZUBUEUAABK
      UBUJUDBUABLUHBLUBUAUJUCUBUAAUIHUJUCHDAUIMNOPQRT $.
      $( [21-Jan-2007] $)

    ${
      ax11indi.2 $e |- ( -. A. x x = y ->
                 ( x = y -> ( ps -> A. x ( x = y -> ps ) ) ) ) $.
      $( Induction step for constructing a substitution instance of ~ ax-11o
         without using ~ ax-11o .  Implication case. $)
      ax11indi $p |- ( -. A. x x = y ->
           ( x = y -> ( ( ph -> ps ) -> A. x ( x = y -> ( ph -> ps ) ) ) ) ) $=
        ( weq wal wn wi wa ax11indn imp pm2.21 imim2i alimi syl6 ax-1 jad ex )
        CDGZCHIZUAABJZUAUCJZCHZJUBUAKZABUEUFAIZUAUGJZCHZUEUBUAUGUIJACDELMUHUDCU
        GUCUAABNOPQUFBUABJZCHZUEUBUABUKJFMUJUDCBUCUABAROPQST $.
        $( [21-Jan-2007] $)
    $}
  $}

  ${
    ax11indalem.1 $e |- ( -. A. x x = y ->
               ( x = y -> ( ph -> A. x ( x = y -> ph ) ) ) ) $.
    $( Lemma for ~ ax11inda2 and ~ ax11inda . $)
    ax11indalem $p |- ( -. A. y y = z -> ( -. A. x x = y ->
               ( x = y -> ( A. z ph -> A. x ( x = y -> A. z ph ) ) ) ) ) $=
      ( weq wal wn wi ax-1 a5i a1i biidd a1d wa alequcom con3i imp hbnae hban
      dral1 imbi2d dral2 3imtr4d alequcoms adantr simplr ax-12 syl2an hba1 ax-4
      adantlr sylan2 alimd syl2anc ax-7 alrimi 19.21t syl albid syl5ib ad2antrr
      wb syld exp31 pm2.61ian ) BDFBGZCDFCGZHZBCFZBGHZVJADGZVJVLIZBGZIZIZIZVGVQ
      VIVGVPVKVGVOVJVODBDBFDGZABGZVJVSIZBGZVLVNVSWAIVRAVTBVSVJJKLAADBVRAMUAZVMV
      TDBBVRVLVSVJWBUBUCUDUENNUFVGHZVIOZVKVJVOWDVKOVJOZVLVJAIZBGZDGZVNWEVKVJDGZ
      VLWHIWDVKVJUGWDVJWIVKWDVJWIWCVRHZDCFDGZHZVJWIIZVIVRVGDBPQWKVHDCPQWJWLWMBC
      DUHRUIZRULVKWIOAWGDVKWIDBCDSVJDUJTWIVKVJAWGIZVJDUKVKVJWOERUMUNUOWDWHVNIVK
      VJWHWFDGZBGWDVNWFDBUPWDWPVMBWCVIBBDBSCDBSTWDWMDGWPVMVCWDWMDWCVIDBDDSCDDST
      WNUQVJADURUSUTVAVBVDVEVF $.
      $( [24-Jan-2007] $)
  $}

  ${
    $d z y $.
    ax11inda2.1 $e |- ( -. A. x x = y ->
               ( x = y -> ( ph -> A. x ( x = y -> ph ) ) ) ) $.
    $( A proof of ~ ax11inda2 that is slightly more direct. $)
    ax11inda2ALT $p |- ( -. A. x x = y ->
               ( x = y -> ( A. z ph -> A. x ( x = y -> A. z ph ) ) ) ) $=
      ( weq wal wn wi ax-1 a5i a1i biidd dral1 imbi2d dral2 a1d wa imp hbnae wb
      3imtr4d alequcoms simplr dveeq1 nalequcoms adantlr hba1 hban sylan2 alimd
      ax-4 syl2anc ax-7 alrimi 19.21t albid syl5ib ad2antrr syld exp31 pm2.61i
      syl ) BDFBGZBCFZBGHZVEADGZVEVGIZBGZIZIZIVDVKVFVDVJVEVJDBDBFDGZABGZVEVMIZB
      GZVGVIVMVOIVLAVNBVMVEJKLAADBVLAMNZVHVNDBBVLVGVMVEVPOPUBUCQQVDHZVFVEVJVQVF
      RVERZVGVEAIZBGZDGZVIVRVFVEDGZVGWAIVQVFVEUDVQVEWBVFVQVEWBVEWBIZDBDBCUEUFZS
      UGVFWBRAVTDVFWBDBCDTVEDUHUIWBVFVEAVTIZVEDULVFVEWEESUJUKUMVQWAVIIVFVEWAVSD
      GZBGVQVIVSDBUNVQWFVHBBDBTVQWCDGWFVHUAVQWCDBDDTWDUOVEADUPVCUQURUSUTVAVB $.
      $( [4-May-2007] $)

    $( Induction step for constructing a substitution instance of ~ ax-11o
       without using ~ ax-11o .  Quantification case.  When ` z ` and ` y ` are
       distinct, this theorem avoids the dummy variables needed by the more
       general ~ ax11inda . $)
    ax11inda2 $p |- ( -. A. x x = y ->
               ( x = y -> ( A. z ph -> A. x ( x = y -> A. z ph ) ) ) ) $=
      ( weq wal wn wi ax-1 a16g syl5 a1d ax11indalem pm2.61i ) CDFCGZBCFZBGHZQA
      DGZQSIZBGZIZIZIPUCRPUBQSTPUASQJTCDBKLMMABCDENO $.
      $( [24-Jan-2007] $)
  $}

  ${
    $d w ph $.  $d w x $.  $d w y $.  $d w z $.
    ax11inda.1 $e |- ( -. A. x x = w ->
               ( x = w -> ( ph -> A. x ( x = w -> ph ) ) ) ) $.
    $( Induction step for constructing a substitution instance of ~ ax-11o
       without using ~ ax-11o .  Quantification case.  (When ` z ` and ` y `
       are distinct, ~ ax11inda2 may be used instead to avoid the dummy
       variable ` w ` in the proof.) $)
    ax11inda $p |- ( -. A. x x = y ->
               ( x = y -> ( A. z ph -> A. x ( x = y -> A. z ph ) ) ) ) $=
      ( weq wal wn wi wex a9e wa ax11inda2 wb dveeq2 imp albid syl imbi12d hba1
      equequ2 a4s notbid adantl imbi1d imbi2d mpbii ex exlimdv mpi pm2.43i ) BC
      GZBHZIZUMADHZUMUPJZBHZJZJZUOECGZEKUOUTJZECLUOVAVBEUOVAVBUOVAMZBEGZBHZIZVD
      UPVDUPJZBHZJZJZJVBABEDFNVCVFUOVJUTVCVABHZVFUOOUOVAVKBCEPQZVKVEUNVKVDUMBVA
      BUAZVAVDUMOZBECBUBZUCZRUDSVCVDUMVIUSVAVNUOVOUEVCVHURUPVCVKVHUROVLVKVGUQBV
      MVKVDUMUPVPUFRSUGTTUHUIUJUKUL $.
      $( [24-Jan-2007] $)
  $}

  $( Part of a study related to ~ ax-12 .  The consequent introduces a new
     variable ` z ` .  There are no distinct variable restrictions. $)
  a12stdy1 $p |- ( A. x x = y -> E. x y = z ) $=
    ( weq wal wex a9e wn ax-10o con3d df-ex 3imtr4g mpi ) ABDAEZBCDZBFZOAFZBCGN
    OHZBEZHRAEZHPQNTSRABIJOBKOAKLM $.
    $( [14-Jan-2008] $)

  $( Part of a study related to ~ ax-12 .  The consequent is quantified with a
     different variable.  There are no distinct variable restrictions. $)
  a12stdy2 $p |- ( A. z ( z = x /\ x = y ) -> A. y y = x ) $=
    ( weq wa wal 19.26 ax-10o alequcom syl6 imp sylbi ) CADZABDZECFMCFZNCFZEBAD
    BFZMNCGOPQOPNAFQNCAHABIJKL $.
    $( [14-Jan-2008] $)

  $( Part of a study related to ~ ax-12 .  The consequent introduces two new
     variables.  There are no distinct variable restrictions. $)
  a12stdy3 $p |- ( A. z ( z = x /\ x = y ) -> A. v E. y x = w ) $=
    ( weq wa wal wex a12stdy2 hbae a12stdy1 alimi 3syl ) CAFABFGCHBAFBHZOEHADFB
    IZEHABCJBAEKOPEBADLMN $.
    $( [14-Jan-2008] $)

  $( Part of a study related to ~ ax-12 .  The second antecedent of ~ ax-12 is
     replaced.  There are no distinct variable restrictions. $)
  a12stdy4 $p |- ( -. A. z z = x -> ( A. y z = x ->
           ( x = y -> A. z x = y ) ) ) $=
    ( weq wal wn wi wa ax-10o alequcoms con3d impcom pm2.21d ax-12 a1dd pm2.61d
    ex ) CADZCEZFZCBDCEZRBEZABDZUCCEGZGZTUAUETUAHUBUDUATUBFUAUBSUBSGBCRBCIJKLMQ
    TUAFUDUBABCNOP $.
    $( [14-Jan-2008] $)

  $( Proof of first hypothesis of ~ a12study . $)
  a12lem1 $p |- ( -. A. z z = y ->
                  ( A. z ( z = x -> z = y ) -> x = y ) ) $=
    ( weq wal wn wi wb equequ1 imbi12d a4s dral2 equid a1bi biimpri syl6bi hbn1
    a1d wa hban hbth a1i ax-12 imp hbimd alrimi equtr ax-8 imim12d ax-gen 19.26
    a4imt sylbir sylancl mpii ex pm2.61i ) CADZCEZCBDZCEFZURUTGZCEZABDZGZGUSVEV
    AUSVCAADZVDGZCEZVDVBVGCACURVBVGHCURURVFUTVDCAAICABIJKLVGVDCVDVGVFVDAMZNOKPR
    USFZVAVEVJVASZVCVFVDVIVKVGVHGZCEZURVBVGGGZCEZVCVGGZVKVLCVJVACURCQUTCQTZVKVF
    VDCVQVFVFCEGVKVFCVIUAUBVJVAVDVDCEGABCUCUDUEUFVNCURVFURUTVDCAAUGCABUHUIUJVMV
    OSVLVNSCEVPVLVNCUKVBVGCAULUMUNUOUPUQ $.
    $( [15-Jan-2008] $)

  $( Proof of second hypothesis of ~ a12study . $)
  a12lem2 $p |- ( A. z ( z = x -> -. z = y ) -> -. x = y ) $=
    ( weq wn wi wal wa wex equcom imbi1i imnan bitri albii alnex equvini con3i
    sylbi ) CADZCBDZEZFZCGZACDZTHZCIZEZABDZEUCUEEZCGUGUBUICUBUDUAFUISUDUACAJKUD
    TLMNUECOMUHUFABCPQR $.
    $( [15-Jan-2008] $)

  ${
    a12study.1 $e |- ( -. A. z z = y
         -> ( A. z ( z = x -> z = y ) -> x = y ) ) $.
    a12study.2 $e |- ( A. z ( z = x -> -. z = y ) -> -. x = y ) $.
    $( Rederivation of axiom ~ ax-12 from two shorter formulas, without using
       ~ ax-12 .  See ~ a12lem1 and ~ a12lem2 for the proofs of the hypotheses
       (using ~ ax-12 ).  This is the only known breakdown of ~ ax-12 into
       shorter formulas.  See ~ a12studyALT for an alternate proof.  Note that
       the proof depends on ~ ax-11o , whose proof ~ ax11o depends on ~ ax-12 ,
       meaning that we would have to replace ~ ax-11 with ~ ax-11o in an
       axiomatization that uses the hypotheses in place of ~ ax-12 .  Whether
       this can be avoided is an open problem. $)
    a12study $p |- ( -. A. z z = x -> ( -. A. z z = y
                     -> ( x = y -> A. z x = y ) ) ) $=
      ( weq wa wex wal wn imnan equid1 ax-8 mpi imim1i sylbir alimi hbn1 hba1
      wi con2i df-ex sylibr hban ax-11o syl5 imp3a alrimd sylan9 exlimd ex syl7
      syl ) ABFZACFZCBFZGZCHZCAFZCIJZUPCIJZUNCIZUNUQJZCIZJURVDUNVDUSUPJZTZCIUNJ
      VCVFCVCUOVETVFUOUPKUSUOVEUSCCFUOCLCACMNOPQEUMUAUQCUBUCUTVAURVBTUTVAGUQVBC
      UTVACUSCRUPCRZUDUNCSUTUQUSUPTZCIZVAVBUTUOUPVIUOUSUTUPVITUOAAFUSALACAMNUPC
      AUEUFUGVAVIUNCVGVHCSDUHUIUJUKUL $.
      $( [15-Jan-2008] $)

    $( Alternate proof of ~ a12study , also without using ~ ax-12 . $)
    a12studyALT $p |- ( -. A. z z = x -> ( -. A. z z = y
             -> ( x = y -> A. z x = y ) ) ) $=
      ( weq wal wn wi wa hbn1 hban con3d wex exnal hba1 ax-11o ax11indn syl5bir
      annim a5i syl8 imp3a exlimd sylan9r hbnd notnot albii 3imtr4g ex ) CAFZCG
      HZCBFZCGHZABFZUOCGZIULUNJZUOHZHZUSCGUOUPUQURCULUNCUKCKZUMCKLUNURUKUMIZCGZ
      HZULURCGZUNVBUODMVCVAHZCNULVDVACOULVEVDCUTURCPVEUKUMHZJULVDUKUMTULUKVFVDU
      LUKVFUKVFIZCGVDUMCAUMCAQRVGURCEUAUBUCSUDSUEUFUOUGZUOUSCVHUHUIUJ $.
      $( [17-Jan-2008] $)
  $}

  ${
    $d w x $.  $d w y $.  $d w z $.
    a12study2.1 $e |- ( -. A. x x = z -> ( w = z -> A. x w = z ) ) $.
    a12study2.2 $e |- ( -. A. x x = y -> ( w = y -> A. x w = y ) ) $.
    $( Reprove ~ ax-12 using ~ dvelimfALT2 , showing that ~ ax-12 can be
       replaced by ~ dveeq2 (whose needed instances are the hypotheses here) if
       we allow distinct variables in axioms other than ~ ax-17 .  (Contributed
       by Andrew Salmon, 21-Jul-2011.) $)
    a12study2 $p |- ( -. A. x x = y
      -> ( -. A. x x = z -> ( y = z -> A. x y = z ) ) ) $=
      ( cv wceq wal wn hbn1 hbim1 ax-17 equequ1 imbi2d dvelimfALT2 19.21 syl6ib
      wi pm2.86d ) AGZBGZHAIJZUACGZHZAIJZUBUDHZUGAIZUCUFUGSZUIAIUFUHSUFDGZUDHZS
      UIABDUFUKAUEAKZELUIDMUJUBHUKUGUFDBCNOFPUFUGAULQRT $.
      $( [21-Jul-2011] $)
  $}

  ${
    a12study3.1 $e |- ( x = y -> E. z ( x = z /\ z = y ) ) $.
    a12study3.2 $e |- ( A. z ( z = x <-> z = y ) -> x = y ) $.
    $( Rederivation of axiom ~ ax-12 from two other formulas, without using
       ~ ax-12 .  See ~ equvini and ~ equveli for the proofs of the hypotheses
       (using ~ ax-12 ).  Although the second hypothesis (when expanded to
       primitives) is longer than ~ ax-12 , an open problem is whether it can
       be derived without ~ ax-12 or from a simpler axiom.

       Note also that the proof depends on ~ ax-11o , whose proof ~ ax11o
       depends on ~ ax-12 , meaning that we would have to replace ~ ax-11 with
       ~ ax-11o in an axiomatization that uses the hypotheses in place of
       ~ ax-12 .  Whether this can be avoided is an open problem. $)
    a12study3 $p |- ( -. A. z z = x -> ( -. A. z z = y
       -> ( x = y -> A. z x = y ) ) ) $=
      ( weq wal wn wi wa wb wex hbn1 hba1 equid1 ax-8 ax-11o syl5 imp3a exlimd
      mpi syl7 ancomsd anim12ii albiim syl6ibr a5i syl6 ex ) CAFZCGHZCBFZCGHZAB
      FZUNCGZIUKUMJZUNUJULKZCGZUOUPUNUJULIZCGZULUJIZCGZJZURUNACFZULJZCLZUPVCDUK
      VFUTUMVBUKVEUTCUJCMUSCNUKVDULUTVDUJUKULUTIVDAAFUJAOACAPUAZULCAQRSTUMVEVBC
      ULCMVACNUMULVDVBUMULVDVBVDUJUMULVBVGUJCBQUBSUCTUDRUJULCUEUFUQUNCEUGUHUI
      $.
      $( [1-Mar-2013] $)
  $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Existential uniqueness
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Declare new symbols needed for uniqueness notation. $)
  $c E! $.  $( Backwards E exclamation point. $)
  $c E* $.  $( Backwards E superscript *. $)

  $( Extend wff definition to include existential uniqueness ("there exists a
     unique ` x ` such that ` ph ` "). $)
  weu $a wff E! x ph $.

  $( Extend wff definition to include uniqueness ("there exists at most one
     ` x ` such that ` ph ` "). $)
  wmo $a wff E* x ph $.

  ${
    $d w x y $.  $d x z $.  $d y ph $.  $d w z ph $.
    $( A soundness justification theorem for ~ df-eu , showing that the
       definition is equivalent to itself with its dummy variable renamed.
       Note that ` y ` and ` z ` needn't be distinct variables.  See
       ~ eujustALT for a proof that provides an example of how it can be
       achieved through the use of ~ dvelim .  (The proof was shortened by
       Andrew Salmon, 9-Jul-2011.) $)
    eujust $p |- ( E. y A. x ( ph <-> x = y )
        <-> E. z A. x ( ph <-> x = z ) ) $=
      ( vw cv wceq wb wal wex equequ2 bibi2d albidv cbvexv bitri ) ABFZCFZGZHZB
      IZCJAPEFZGZHZBIZEJAPDFZGZHZBIZDJTUDCEQUAGZSUCBUIRUBACEBKLMNUDUHEDUAUEGZUC
      UGBUJUBUFAEDBKLMNO $.
      $( [9-Jul-2011] $) $( [11-Mar-2010] $)

    $( A soundness justification theorem for ~ df-eu , showing that the
       definition is equivalent to itself with its dummy variable renamed.
       Note that ` y ` and ` z ` needn't be distinct variables.  While this
       isn't strictly necessary for soundness, the proof provides an example of
       how it can be achieved through the use of ~ dvelim . $)
    eujustALT $p |- ( E. y A. x ( ph <-> x = y )
        <-> E. z A. x ( ph <-> x = z ) ) $=
      ( vw weq wal wb wex equequ2 bibi2d albidv wn hbnae wi ax-17 notbid dvelim
      a4s df-ex drex1 alrimi nalequcoms a1i cbv2 syl 3bitr4g pm2.61i ) CDFZCGZA
      BCFZHZBGZCIZABDFZHZBGZDIZHUMUQCDUIUMUQHCUIULUPBUIUKUOACDBJKLZSUAUJMZUMMZC
      GZMUQMZDGZMUNURUTVBVDUTUTDGZCGVBVDHUTVECCDCNCDDNUBUTVAVCCDVAVADGODCABEFZH
      ZBGZMZVADCEVIDPECFZVHUMVJVGULBVJVFUKAECBJKLQRUCVIVCCDEVICPEDFZVHUQVKVGUPB
      VKVFUOAEDBJKLQRUIVAVCHOUTUIUMUQUSQUDUEUFQUMCTUQDTUGUH $.
      $( [11-Mar-2010] $)
  $}

  ${
    $d x y $.  $d y ph $.
    $( Define existential uniqueness, i.e.  "there exists exactly one ` x `
       such that ` ph ` ."  Definition 10.1 of [BellMachover] p. 97; also
       Definition *14.02 of [WhiteheadRussell] p. 175.  Other possible
       definitions are given by ~ eu1 , ~ eu2 , ~ eu3 , and ~ eu5 (which in
       some cases we show with a hypothesis ` ph -> A. y ph ` in place of a
       distinct variable condition on ` y ` and ` ph ` ).  Double uniqueness is
       tricky: ` E! x E! y ph ` does not mean "exactly one ` x ` and one
       ` y ` " (see ~ 2eu4 ). $)
    df-eu $a |- ( E! x ph <-> E. y A. x ( ph <-> x = y ) ) $.
  $}

  $( Define "there exists at most one ` x ` such that ` ph ` ."  Here we define
     it in terms of existential uniqueness.  Notation of [BellMachover] p. 460,
     whose definition we show as ~ mo3 .  For other possible definitions see
     ~ mo2 and ~ mo4 . $)
  df-mo $a |- ( E* x ph <-> ( E. x ph -> E! x ph ) ) $.

  ${
    $d x y z $.  $d ph z $.
    euf.1 $e |- ( ph -> A. y ph ) $.
    $( A version of the existential uniqueness definition with a hypothesis
       instead of a distinct variable condition. $)
    euf $p |- ( E! x ph <-> E. y A. x ( ph <-> x = y ) ) $=
      ( vz weu weq wb wal wex df-eu ax-17 hbbi hbal equequ2 bibi2d albidv cbvex
      bitri ) ABFABEGZHZBIZEJABCGZHZBIZCJABEKUBUEECUACBATCDTCLMNUEELECGZUAUDBUF
      TUCAECBOPQRS $.
      $( [12-Aug-1993] $)
  $}

  ${
    $d x y $.  $d y ph $.  $d y ps $.  $d y ch $.
    eubid.1 $e |- ( ph -> A. x ph ) $.
    eubid.2 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Formula-building rule for uniqueness quantifier (deduction rule). $)
    eubid $p |- ( ph -> ( E! x ps <-> E! x ch ) ) $=
      ( vy weq wb wal wex weu bibi1d albid exbidv df-eu 3bitr4g ) ABDGHZIZDJZGK
      CRIZDJZGKBDLCDLATUBGASUADEABCRFMNOBDGPCDGPQ $.
      $( [9-Jul-1994] $)
  $}

  ${
    $d x ph $.
    eubidv.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Formula-building rule for uniqueness quantifier (deduction rule). $)
    eubidv $p |- ( ph -> ( E! x ps <-> E! x ch ) ) $=
      ( ax-17 eubid ) ABCDADFEG $.
      $( [9-Jul-1994] $)
  $}

  ${
    eubii.1 $e |- ( ph <-> ps ) $.
    $( Introduce uniqueness quantifier to both sides of an equivalence. $)
    eubii $p |- ( E! x ph <-> E! x ps ) $=
      ( weq weu wb equid hbequid a1i eubid ax-mp ) CCEZACFBCFGCHMABCCCIABGMDJKL
      $.
      $( [9-Jul-1994] $)
  $}

  ${
    $d x y $.  $d y ph $.
    $( Bound-variable hypothesis builder for uniqueness. $)
    hbeu1 $p |- ( E! x ph -> A. x E! x ph ) $=
      ( vy weu weq wb wal wex df-eu hba1 hbex hbxfrbi ) ABDABCEFZBGZCHBABCINBCM
      BJKL $.
      $( [9-Jul-1994] $)
  $}

  ${
    $d y z $.  $d x z $.  $d z ph $.
    hbeu.1 $e |- ( ph -> A. x ph ) $.
    $( Bound-variable hypothesis builder for "at most one."  Note that ` x `
       and ` y ` needn't be distinct (this makes the proof more difficult). $)
    hbeu $p |- ( E! y ph -> A. x E! y ph ) $=
      ( vz weu weq wb wal wex df-eu wi hba1 ax10o alequcoms wn hbnae a1i dveeq1
      syl5 hbbid hbald pm2.61i hbex hbxfrbi ) ACFACEGZHZCIZEJBACEKUHBEBCGBIZUHU
      HBIZLUHUHCIZUIUJUGCMUKUJLCBUHCBNOTUIPZUGBCBCCQULAUFBBCBQAABILULDRBCESUAUB
      UCUDUE $.
      $( [8-Mar-1995] $)
  $}

  ${
    $d y z $.  $d x z $.  $d z ph $.  $d z ps $.
    hbeud.1 $e |- ( ph -> A. x ph ) $.
    hbeud.2 $e |- ( ph -> A. y ph ) $.
    hbeud.3 $e |- ( ph -> ( ps -> A. x ps ) ) $.
    $( Deduction version of ~ hbeu . $)
    hbeud $p |- ( ph -> ( E! y ps -> A. x E! y ps ) ) $=
      ( vz cv wceq wb wal wex weu ax-17 wi wn wa hbnae hban adantr dveeq1 hbbid
      adantl hbald hba1 ax10o alequcoms syl5 pm2.61d2 hbexd df-eu albii 3imtr4g
      ex ) ABDIZHIJZKZDLZHMZUTCLBDNZVACLAUSCHAHOACIUPJCLZUSUSCLZPZAVBQZVDAVERZU
      RCDAVEDFCDDSTVFBUQCAVECECDCSTABBCLPVEGUAVEUQUQCLPACDHUBUDUCUEUOUSUSDLZVBV
      CURDUFVGVCPDCUSDCUGUHUIUJUKBDHULZVAUTCVHUMUN $.
      $( [15-Feb-2013] $)
  $}

  ${
    $d w y z $.  $d ph z w $.  $d w x z $.
    sb8eu.1 $e |- ( ph -> A. y ph ) $.
    $( Variable substitution in uniqueness quantifier.  (Unnecessary distinct
       variable restrictions were removed by Andrew Salmon, 9-Jul-2011.) $)
    sb8eu $p |- ( E! x ph <-> E! y [ y / x ] ph ) $=
      ( vz vw cv wceq wal wex wsbc weu ax-17 sb8 sbbi hbsb equsb3 hbxfrbi df-eu
      wb hbbi sbequ cbval sblbis albii 3bitri exbii 3bitr4i ) ABGEGZHZTZBIZEJAB
      CGZKZUMUIHZTZCIZEJABLUNCLULUQEULUKBFGZKZFIUKBUMKZCIUQUKBFUKFMNUSUTFCUSABU
      RKZUJBURKZTCAUJBFOVAVBCABFCDPVBURUIHZCFBEQVCCMRUARUTFMUKFCBUBUCUTUPCUJUOA
      BCCBEQUDUEUFUGABESUNCESUH $.
      $( [9-Jul-2011] $) $( [7-Aug-1994] $)
  $}

  ${
    cbveu.1 $e |- ( ph -> A. y ph ) $.
    cbveu.2 $e |- ( ps -> A. x ps ) $.
    cbveu.3 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( Rule used to change bound variables, using implicit substitition.
       (Unnecessary distinct variable restrictions were removed by Andrew
       Salmon, 8-Jun-2011.) $)
    cbveu $p |- ( E! x ph <-> E! y ps ) $=
      ( weu wsb sb8eu sbie eubii bitri ) ACHACDIZDHBDHACDEJNBDABCDFGKLM $.
      $( [9-Jul-2011] $) $( [25-Nov-1994] $)
  $}

  ${
    $d x y $.
    eu1.1 $e |- ( ph -> A. y ph ) $.
    $( An alternate way to express uniqueness used by some authors.  Exercise
       2(b) of [Margaris] p. 110. $)
    eu1 $p |- ( E! x ph <->
                E. x ( ph /\ A. y ( [ y / x ] ph -> x = y ) ) ) $=
      ( wsb weu weq wb wal wex wi wa hbs1 euf sb8eu equcom imbi2i albii 3bitr4i
      sb6rf anbi12i ancom albiim exbii ) ABCEZCFUECBGZHCIZBJABFAUEBCGZKZCIZLZBJ
      UECBABCMNABCDOUKUGBUJALUEUFKZCIZUFUEKCIZLUKUGUJUMAUNUIULCUHUFUEBCPQRABCDT
      UAAUJUBUEUFCUCSUDS $.
      $( [20-Aug-1993] $)
  $}

  ${
    $d x y z $.  $d ph z $.
    mo.1 $e |- ( ph -> A. y ph ) $.
    $( Equivalent definitions of "there exists at most one." $)
    mo $p |- ( E. y A. x ( ph -> x = y ) <->
               A. x A. y ( ( ph /\ [ y / x ] ph ) -> x = y ) ) $=
      ( vz weq wi wal wex wsb wa ax-17 hbim hbal cbv3 syl sylbir alimi wn hbn
      equequ2 imbi2d albidv cbvex hbs1 sbequ2 ax-8 imim12d ancli aaan prth syl6
      sylibr equtr2 2alimi exlimiv impexp bi2.04 bitri 2albii eximi a7s syl5com
      alim exim syl5bi alnex sbequ1 equcoms con3d pm2.21 19.8a 3syl a1d pm2.61i
      impbii ) ABCFZGZBHZCIZAABCJZKZVQGZCHBHZVTABEFZGZBHZEIWDWGVSECWFCBAWECDWEC
      LMZNVSELECFZWFVRBWIWEVQAECBUAUBUCUDWGWDEWGWFWACEFZGZKZCHBHZWDWGWGWKCHZKWM
      WGWNWFWKBCWHWAWJBABCUEZWJBLMZVQWAAWEWJABCUFBCEUGUHOUIWFWKBCWHWPUJUMWLWCBC
      WLWBWEWJKVQAWEWAWJUKBCEUNULUOPUPQWACIZWDVTGWDWAVRGZCHBHZWQVTWCWRBCWCAWAVQ
      GGWRAWAVQUQAWAVQURUSUTWQWABHZCIZWSVTWAWTCWOVAWSWTVSGZCHZXAVTGWRXCCBWRBHXB
      CWAVRBVDRVBWTVSCVEPVCVFWQSZVTWDXDWASZCHZVTWACVGXFASZBHVSVTXEXGCBWABWOTACD
      TCBFAWAAWAGBCABCVHVIVJOXGVRBAVQVKRVSCVLVMQVNVOVP $.
      $( [7-Aug-1994] $)
  $}

  ${
    $d x y $.  $d ph y $.
    $( Existential uniqueness implies existence.  (The proof was shortened by
       Andrew Salmon, 9-Jul-2011.) $)
    euex $p |- ( E! x ph -> E. x ph ) $=
      ( vy weu wsb weq wi wal wa wex ax-17 eu1 exsimpl sylbi ) ABDAABCEBCFGCHZI
      BJABJABCACKLAOBMN $.
      $( [9-Jul-2011] $) $( [15-Sep-1993] $)
  $}

  ${
    $d x y $.
    eumo0.1 $e |- ( ph -> A. y ph ) $.
    $( Existential uniqueness implies "at most one." $)
    eumo0 $p |- ( E! x ph -> E. y A. x ( ph -> x = y ) ) $=
      ( weu weq wb wal wex wi euf bi1 alimi eximi sylbi ) ABEABCFZGZBHZCIAPJZBH
      ZCIABCDKRTCQSBAPLMNO $.
      $( [8-Jul-1994] $)
  $}

  ${
    $d x y $.
    eu2.1 $e |- ( ph -> A. y ph ) $.
    $( An alternate way of defining existential uniqueness.  Definition 6.10 of
       [TakeutiZaring] p. 26. $)
    eu2 $p |- ( E! x ph <->
    ( E. x ph /\ A. x A. y ( ( ph /\ [ y / x ] ph ) -> x = y ) ) ) $=
      ( weu wex wsb wa weq wi wal euex eumo0 mo sylib 19.29r impexp albii 19.21
      jca bitri anbi2i abai bitr4i exbii eu1 sylibr impbii ) ABEZABFZAABCGZHBCI
      ZJZCKZBKZHZUIUJUOABLUIAULJBKCFUOABCDMABCDNOTUPAUKULJZCKZHZBFZUIUPAUNHZBFU
      TAUNBPVAUSBVAAAURJZHUSUNVBAUNAUQJZCKVBUMVCCAUKULQRAUQCDSUAUBAURUCUDUEOABC
      DUFUGUH $.
      $( [8-Jul-1994] $)
  $}

  ${
    $d x y $.
    eu3.1 $e |- ( ph -> A. y ph ) $.
    $( An alternate way to express existential uniqueness. $)
    eu3 $p |- ( E! x ph <->
                ( E. x ph /\ E. y A. x ( ph -> x = y ) ) ) $=
      ( weu wex wsb wa weq wi wal eu2 mo anbi2i bitr4i ) ABEABFZAABCGHBCIZJCKBK
      ZHPAQJBKCFZHABCDLSRPABCDMNO $.
      $( [8-Jul-1994] $)
  $}

  ${
    euor.1 $e |- ( ph -> A. x ph ) $.
    $( Introduce a disjunct into a uniqueness quantifier. $)
    euor $p |- ( ( -. ph /\ E! x ps ) -> E! x ( ph \/ ps ) ) $=
      ( wn weu wo hbn biorf eubid biimpa ) AEZBCFABGZCFLBMCACDHABIJK $.
      $( [21-Oct-2005] $)
  $}

  ${
    $d x ph $.
    $( Introduce a disjunct into a uniqueness quantifier. $)
    euorv $p |- ( ( -. ph /\ E! x ps ) -> E! x ( ph \/ ps ) ) $=
      ( ax-17 euor ) ABCACDE $.
      $( [23-Mar-1995] $)
  $}

  ${
    $d x y $.
    mo2.1 $e |- ( ph -> A. y ph ) $.
    $( Alternate definition of "at most one." $)
    mo2 $p |- ( E* x ph <-> E. y A. x ( ph -> x = y ) ) $=
      ( wmo wex weu wi weq wal df-mo alnex pm2.21 alimi 19.8a syl sylbir eumo0
      wn ja eu3 simplbi2com impbii bitri ) ABEABFZABGZHZABCIZHZBJZCFZABKUGUKUEU
      FUKUESASZBJZUKABLUMUJUKULUIBAUHMNUJCOPQABCDRTUFUEUKABCDUAUBUCUD $.
      $( [8-Mar-1995] $)
  $}

  ${
    $d w x z $.  $d w y z $.  $d w ph $.
    $( Substitution into "at most one".  (Contributed by Jeff Madsen,
       2-Sep-2009.) $)
    sbmo $p |- ( [ y / x ] E* z ph <-> E* z [ y / x ] ph ) $=
      ( vw cv wceq wi wal wex wsbc wmo sbex ax-17 sblim sbalv exbii bitri sbbii
      mo2 3bitr4i ) ADFEFGZHZDIZEJZBCFZKZABUFKZUBHZDIZEJZADLZBUFKUHDLUGUDBUFKZE
      JUKUDEBCMUMUJEUCUIBCDAUBBCUBBNOPQRULUEBCADEAENTSUHDEUHENTUA $.
      $( [2-Sep-2009] $)
  $}

  ${
    $d x y $.
    mo3.1 $e |- ( ph -> A. y ph ) $.
    $( Alternate definition of "at most one."  Definition of [BellMachover]
       p. 460, except that definition has the side condition that ` y ` not
       occur in ` ph ` in place of our hypothesis. $)
    mo3 $p |- ( E* x ph <->
               A. x A. y ( ( ph /\ [ y / x ] ph ) -> x = y ) ) $=
      ( wmo weq wi wal wex wsb wa mo2 mo bitri ) ABEABCFZGBHCIAABCJKOGCHBHABCDL
      ABCDMN $.
      $( [8-Mar-1995] $)
  $}

  ${
    $d x y $.  $d y ph $.
    mo4f.1 $e |- ( ps -> A. x ps ) $.
    mo4f.2 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( "At most one" expressed using implicit substitution. $)
    mo4f $p |- ( E* x ph <-> A. x A. y ( ( ph /\ ps ) -> x = y ) ) $=
      ( wmo wsb wa weq wi wal ax-17 mo3 sbie anbi2i imbi1i 2albii bitri ) ACGAA
      CDHZIZCDJZKZDLCLABIZUBKZDLCLACDADMNUCUECDUAUDUBTBAABCDEFOPQRS $.
      $( [10-Apr-2004] $)
  $}

  ${
    $d x y $.  $d y ph $.  $d x ps $.
    mo4.1 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( "At most one" expressed using implicit substitution. $)
    mo4 $p |- ( E* x ph <-> A. x A. y ( ( ph /\ ps ) -> x = y ) ) $=
      ( ax-17 mo4f ) ABCDBCFEG $.
      $( [26-Jul-1995] $)
  $}

  ${
    mobid.1 $e |- ( ph -> A. x ph ) $.
    mobid.2 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Formula-building rule for "at most one" quantifier (deduction rule). $)
    mobid $p |- ( ph -> ( E* x ps <-> E* x ch ) ) $=
      ( wex weu wi wmo exbid eubid imbi12d df-mo 3bitr4g ) ABDGZBDHZICDGZCDHZIB
      DJCDJAPRQSABCDEFKABCDEFLMBDNCDNO $.
      $( [8-Mar-1995] $)
  $}

  ${
    mobii.1 $e |- ( ps <-> ch ) $.
    $( Formula-building rule for "at most one" quantifier (inference rule). $)
    mobii $p |- ( E* x ps <-> E* x ch ) $=
      ( weq wmo wb equid hbequid a1i mobid ax-mp ) CCEZACFBCFGCHMABCCCIABGMDJKL
      $.
      $( [9-Mar-1995] $)
  $}

  $( Bound-variable hypothesis builder for "at most one." $)
  hbmo1 $p |- ( E* x ph -> A. x E* x ph ) $=
    ( wmo wex weu wi df-mo hbe1 hbeu1 hbim hbxfrbi ) ABCABDZABEZFBABGLMBABHABIJ
    K $.
    $( [8-Mar-1995] $)

  ${
    hbmo.1 $e |- ( ph -> A. x ph ) $.
    $( Bound-variable hypothesis builder for "at most one." $)
    hbmo $p |- ( E* y ph -> A. x E* y ph ) $=
      ( wmo wex weu wi df-mo hbex hbeu hbim hbxfrbi ) ACEACFZACGZHBACINOBABCDJA
      BCDKLM $.
      $( [9-Mar-1995] $)
  $}

  ${
    cbvmo.1 $e |- ( ph -> A. y ph ) $.
    cbvmo.2 $e |- ( ps -> A. x ps ) $.
    cbvmo.3 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( Rule used to change bound variables, using implicit substitition.
       (Unnecessary distinct variable restrictions were removed by Andrew
       Salmon, 8-Jun-2011.) $)
    cbvmo $p |- ( E* x ph <-> E* y ps ) $=
      ( wex weu wi wmo cbvex cbveu imbi12i df-mo 3bitr4i ) ACHZACIZJBDHZBDIZJAC
      KBDKQSRTABCDEFGLABCDEFGMNACOBDOP $.
      $( [9-Jul-2011] $) $( [9-Mar-1995] $)
  $}

  ${
    $d x y $.  $d y ph $.
    $( Uniqueness in terms of "at most one." $)
    eu5 $p |- ( E! x ph <-> ( E. x ph /\ E* x ph ) ) $=
      ( vy weu wex weq wi wal wa wmo ax-17 eu3 mo2 anbi2i bitr4i ) ABDABEZABCFG
      BHCEZIPABJZIABCACKZLRQPABCSMNO $.
      $( [23-Mar-1995] $)
  $}

  ${
    $d x y $.  $d y ph $.  $d x ps $.
    eu4.1 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( Uniqueness using implicit substitution. $)
    eu4 $p |- ( E! x ph <-> ( E. x ph /\
             A. x A. y ( ( ph /\ ps ) -> x = y ) ) ) $=
      ( weu wex wmo wa weq wi wal eu5 mo4 anbi2i bitri ) ACFACGZACHZIQABICDJKDL
      CLZIACMRSQABCDENOP $.
      $( [26-Jul-1995] $)
  $}

  $( Existential uniqueness implies "at most one." $)
  eumo $p |- ( E! x ph -> E* x ph ) $=
    ( weu wex wmo eu5 simprbi ) ABCABDABEABFG $.
    $( [23-Mar-1995] $)

  ${
    eumoi.1 $e |- E! x ph $.
    $( "At most one" inferred from existential uniqueness. $)
    eumoi $p |- E* x ph $=
      ( weu wmo eumo ax-mp ) ABDABECABFG $.
      $( [5-Apr-1995] $)
  $}

  $( Existence in terms of "at most one" and uniqueness. $)
  exmoeu $p |- ( E. x ph <-> ( E* x ph -> E! x ph ) ) $=
    ( wex wmo weu wi df-mo biimpi com12 biimpri euex imim12i peirce syl impbii
    ) ABCZABDZABEZFZQPRQPRFZABGZHISTPFPTQRPQTUAJABKLPRMNO $.
    $( [5-Apr-2004] $)

  $( Existence implies "at most one" is equivalent to uniqueness. $)
  exmoeu2 $p |- ( E. x ph -> ( E* x ph <-> E! x ph ) ) $=
    ( weu wex wmo eu5 baibr ) ABCABDABEABFG $.
    $( [5-Apr-2004] $)

  $( Absorption of existence condition by "at most one." $)
  moabs $p |- ( E* x ph <-> ( E. x ph -> E* x ph ) ) $=
    ( wex weu wi wmo pm5.4 df-mo imbi2i 3bitr4ri ) ABCZKABDZEZEMKABFZENKLGNMKAB
    HZIOJ $.
    $( [4-Nov-2002] $)

  $( Something exists or at most one exists. $)
  exmo $p |- ( E. x ph \/ E* x ph ) $=
    ( wex wmo wn weu wi pm2.21 df-mo sylibr orri ) ABCZABDZLELABFZGMLNHABIJK $.
    $( [8-Mar-1995] $)

  ${
    $d x y $.  $d y ph $.  $d y ps $.
    $( "At most one" is preserved through implication (notice wff reversal). $)
    immo $p |- ( A. x ( ph -> ps ) -> ( E* x ps -> E* x ph ) ) $=
      ( vy wi wal weq wex wmo imim1 al2imi eximdv ax-17 mo2 3imtr4g ) ABEZCFZBC
      DGZEZCFZDHAREZCFZDHBCIACIQTUBDPSUACABRJKLBCDBDMNACDADMNO $.
      $( [22-Apr-1995] $)
  $}

  ${
    immoi.1 $e |- ( ph -> ps ) $.
    $( "At most one" is preserved through implication (notice wff reversal). $)
    immoi $p |- ( E* x ps -> E* x ph ) $=
      ( wi wmo immo mpg ) ABEBCFACFECABCGDH $.
      $( [15-Feb-2006] $)
  $}

  ${
    $d x y $.  $d x y ph $.  $d y ps $.
    $( Move antecedent outside of "at most one." $)
    moimv $p |- ( E* x ( ph -> ps ) -> ( ph -> E* x ps ) ) $=
      ( vy wi wmo weq wal wex ax-1 a1i imim1d alimdv eximdv ax-17 3imtr4g com12
      mo2 ) AABEZCFZBCFZASCDGZEZCHZDIBUBEZCHZDITUAAUDUFDAUCUECABSUBBSEABAJKLMNS
      CDSDORBCDBDORPQ $.
      $( [28-Jul-1995] $)
  $}

  $( Uniqueness implies "at most one" through implication. $)
  euimmo $p |- ( A. x ( ph -> ps ) -> ( E! x ps -> E* x ph ) ) $=
    ( weu wmo wi wal eumo immo syl5 ) BCDBCEABFCGACEBCHABCIJ $.
    $( [22-Apr-1995] $)

  $( Add existential uniqueness quantifiers to an implication.  Note the
     reversed implication in the antecedent.  (The proof was shortened by
     Andrew Salmon, 14-Jun-2011.) $)
  euim $p |- ( ( E. x ph /\ A. x ( ph -> ps ) ) -> ( E! x ps -> E! x ph ) ) $=
    ( wex wi wal wa weu wmo ax-1 euimmo anim12ii eu5 syl6ibr ) ACDZABECFZGBCHZO
    ACIZGACHOQOPROQJABCKLACMN $.
    $( [14-Jun-2011] $) $( [19-Oct-2005] $)

  $( "At most one" is still the case when a conjunct is added. $)
  moan $p |- ( E* x ph -> E* x ( ps /\ ph ) ) $=
    ( wa simpr immoi ) BADACBAEF $.
    $( [22-Apr-1995] $)

  ${
    moani.1 $e |- E* x ph $.
    $( "At most one" is still true when a conjunct is added. $)
    moani $p |- E* x ( ps /\ ph ) $=
      ( wmo wa moan ax-mp ) ACEBAFCEDABCGH $.
      $( [9-Mar-1995] $)
  $}

  $( "At most one" is still the case when a disjunct is removed. $)
  moor $p |- ( E* x ( ph \/ ps ) -> E* x ph ) $=
    ( wo orc immoi ) AABDCABEF $.
    $( [5-Apr-2004] $)

  $( "At most one" imports disjunction to conjunction.  (The proof was
     shortened by Andrew Salmon, 9-Jul-2011.) $)
  mooran1 $p |- ( ( E* x ph \/ E* x ps ) -> E* x ( ph /\ ps ) ) $=
    ( wmo wa simpl immoi moan jaoi ) ACDABEZCDBCDJACABFGBACHI $.
    $( [9-Jul-2011] $) $( [5-Apr-2004] $)

  $( "At most one" exports disjunction to conjunction.  (The proof was
     shortened by Andrew Salmon, 9-Jul-2011.) $)
  mooran2 $p |- ( E* x ( ph \/ ps ) -> ( E* x ph /\ E* x ps ) ) $=
    ( wo wmo moor olc immoi jca ) ABDZCEACEBCEABCFBJCBAGHI $.
    $( [9-Jul-2011] $) $( [5-Apr-2004] $)

  ${
    $d x y $.  $d y ph $.  $d y ps $.
    moanim.1 $e |- ( ph -> A. x ph ) $.
    $( Introduction of a conjunct into "at most one" quantifier. $)
    moanim $p |- ( E* x ( ph /\ ps ) <-> ( ph -> E* x ps ) ) $=
      ( vy wa weq wi wal wex impexp albii 19.21 bitri exbii ax-17 imbi2i 19.37v
      wmo mo2 bitr4i 3bitr4i ) ABFZCEGZHZCIZEJABUDHZCIZHZEJZUCCSABCSZHZUFUIEUFA
      UGHZCIUIUEUMCABUDKLAUGCDMNOUCCEUCEPTULAUHEJZHUJUKUNABCEBEPTQAUHERUAUB $.
      $( [3-Dec-2001] $)

    $( Introduction of a conjunct into uniqueness quantifier.  (The proof was
       shortened by Andrew Salmon, 9-Jul-2011.) $)
    euan $p |- ( E! x ( ph /\ ps ) <-> ( ph /\ E! x ps ) ) $=
      ( wa weu wex wmo simpl exlimi adantr simpr eximi hbe1 ancrd impbid2 mobid
      a1d biimpa eu5 jca32 anbi2i 3imtr4i ibar eubid impbii ) ABEZCFZABCFZEZUGC
      GZUGCHZEZABCGZBCHZEZEUHUJUMAUNUOUKAULUGACDABIJZKUKUNULUGBCABLZMKUKULUOUKU
      GBCUGCNUKUGBURUKBAUKABUQROPQSUAUGCTUIUPABCTUBUCAUIUHABUGCDABUDUESUF $.
      $( [9-Jul-2011] $) $( [19-Feb-2005] $)
  $}

  ${
    $d x y ph $.  $d y ps $.
    $( Introduction of a conjunct into "at most one" quantifier. $)
    moanimv $p |- ( E* x ( ph /\ ps ) <-> ( ph -> E* x ps ) ) $=
      ( ax-17 moanim ) ABCACDE $.
      $( [23-Mar-1995] $)
  $}

  $( Nested "at most one" and uniqueness quantifiers. $)
  moaneu $p |- E* x ( ph /\ E! x ph ) $=
    ( weu wa wmo wi eumo hbeu1 moanim mpbir ancom mobii ) AABCZDZBEMADZBEZPMABE
    FABGMABABHIJNOBAMKLJ $.
    $( [25-Jan-2006] $)

  $( Nested "at most one" quantifiers. $)
  moanmo $p |- E* x ( ph /\ E* x ph ) $=
    ( wmo wa wi id hbmo1 moanim mpbir ancom mobii ) AABCZDZBCLADZBCZOLLELFLABAB
    GHIMNBALJKI $.
    $( [25-Jan-2006] $)

  ${
    $d x ph $.
    $( Introduction of a conjunct into uniqueness quantifier. $)
    euanv $p |- ( E! x ( ph /\ ps ) <-> ( ph /\ E! x ps ) ) $=
      ( ax-17 euan ) ABCACDE $.
      $( [23-Mar-1995] $)
  $}

  ${
    $d x y $.  $d y ph $.  $d y ps $.
    $( "At most one" picks a variable value, eliminating an existential
       quantifier. $)
    mopick $p |- ( ( E* x ph /\ E. x ( ph /\ ps ) ) -> ( ph -> ps ) ) $=
      ( vy wa wex wmo wi wsb ax-17 hbs1 hban weq sbequ12 anbi12d cbvex wal ax-4
      mo3 sylbi a4s sbequ2 imim2i exp3a com4t imp syl5 exlimiv impcom ) ABEZCFZ
      ACGZABHZUKACDIZBCDIZEZDFULUMHZUJUPCDUJDJUNUOCACDKBCDKLCDMZAUNBUOACDNBCDNO
      PUPUQDULAUNEZURHZUPUMULUTDQZCQUTACDADJSVAUTCUTDRUATUNUOUTUMHUTAUNUOBUTAUN
      UOBHZURVBUSBCDUBUCUDUEUFUGUHTUI $.
      $( [27-Jan-1997] $)
  $}

  $( Existential uniqueness "picks" a variable value for which another wff is
     true.  If there is only one thing ` x ` such that ` ph ` is true, and
     there is also an ` x ` (actually the same one) such that ` ph ` and ` ps `
     are both true, then ` ph ` implies ` ps ` regardless of ` x ` .  This
     theorem can be useful for eliminating existential quantifiers in a
     hypothesis.  Compare Theorem *14.26 in [WhiteheadRussell] p. 192. $)
  eupick $p |- ( ( E! x ph /\ E. x ( ph /\ ps ) ) -> ( ph -> ps ) ) $=
    ( weu wmo wa wex wi eumo mopick sylan ) ACDACEABFCGABHACIABCJK $.
    $( [10-Jul-1994] $)

  $( Version of ~ eupick with closed formulas. $)
  eupicka $p |- ( ( E! x ph /\ E. x ( ph /\ ps ) ) -> A. x ( ph -> ps ) ) $=
    ( weu wa wex wi hbeu1 hbe1 hban eupick alrimi ) ACDZABEZCFZEABGCMOCACHNCIJA
    BCKL $.
    $( [6-Sep-2008] $)

  $( Existential uniqueness "pick" showing wff equivalence. $)
  eupickb $p |- ( ( E! x ph /\ E! x ps /\ E. x ( ph /\ ps ) ) ->
               ( ph <-> ps ) ) $=
    ( weu wa wex w3a wi eupick 3adant2 3simpc pm3.22 eximi anim2i 3syl impbid )
    ACDZBCDZABEZCFZGZABQTABHRABCIJUARTERBAEZCFZEBAHQRTKTUCRSUBCABLMNBACIOP $.
    $( [25-Nov-1994] $)

  $( Theorem *14.26 in [WhiteheadRussell] p. 192.  (Contributed by Andrew
     Salmon, 11-Jul-2011.) $)
  eupickbi $p |- ( E! x ph -> ( E. x ( ph /\ ps ) <-> A. x ( ph -> ps ) ) ) $=
    ( weu wa wex wi wal eupicka ex hba1 wb ancl simpl impbid1 eubid euex syl6bi
    a4s com12 impbid ) ACDZABEZCFZABGZCHZUBUDUFABCIJUFUBUDUFUBUCCDUDUFAUCCUECKU
    EAUCLCUEAUCABMABNOSPUCCQRTUA $.
    $( [11-Jul-2011] $)

  $( "At most one" can show the existence of a common value.  In this case we
     can infer existence of conjunction from a conjunction of existence, and it
     is one way to achieve the converse of ~ 19.40 .  (The proof was shortened
     by Andrew Salmon, 9-Jul-2011.) $)
  mopick2 $p |- ( ( E* x ph /\ E. x ( ph /\ ps ) /\ E. x ( ph /\ ch ) ) ->
                E. x ( ph /\ ps /\ ch ) ) $=
    ( wmo wa wex w3a hbmo1 hbe1 mopick ancld anim1d df-3an syl6ibr eximd 3impia
    hban ) ADEZABFZDGZACFZDGABCHZDGSUAFZUBUCDSUADADITDJRUDUBTCFUCUDATCUDABABDKL
    MABCNOPQ $.
    $( [9-Jul-2011] $) $( [5-Apr-2004] $)

  $( Introduce or eliminate a disjunct in a uniqueness quantifier.  (The proof
     was shortened by Andrew Salmon, 9-Jul-2011.) $)
  euor2 $p |- ( -. E. x ph -> ( E! x ( ph \/ ps ) <-> E! x ps ) ) $=
    ( wex wn wo hbe1 hbn wb 19.8a con3i orel1 olc impbid1 syl eubid ) ACDZEZABF
    ZBCQCACGHRAEZSBIAQACJKTSBABLBAMNOP $.
    $( [9-Jul-2011] $) $( [21-Oct-2005] $)

  ${
    moexex.1 $e |- ( ph -> A. y ph ) $.
    $( "At most one" double quantification. $)
    moexex $p |- ( ( E* x ph /\ A. x E* y ps ) -> E* y E. x ( ph /\ ps ) ) $=
      ( wmo wal wa wex wi hbmo1 hba1 hbe1 hbmo hbim mopick ex exlimi wn a1d ori
      com3r alrimd immo a4sd syl6 hbex exsimpl con3i exmo syl pm2.61i imp ) ACF
      ZBDFZCGZABHZCIZDFZACIZUNUPUSJZJZAVBCUNVACACKUPUSCUOCLURCDUQCMNOOAUNURBJZD
      GZVAAUNVCDEADCENUNURABUNURABJABCPQUBUCVDUOUSCURBDUDUEUFRUTSZVAUNVEUSUPVEU
      RDIZSUSVFUTURUTDADCEUGABCUHRUIVFUSURDUJUAUKTTULUM $.
      $( [3-Dec-2001] $)
  $}

  ${
    $d y ph $.
    $( "At most one" double quantification. $)
    moexexv $p |- ( ( E* x ph /\ A. x E* y ps ) -> E* y E. x ( ph /\ ps ) ) $=
      ( ax-17 moexex ) ABCDADEF $.
      $( [26-Jan-1997] $)
  $}

  $( Double quantification with "at most one." $)
  2moex $p |- ( E* x E. y ph -> A. y E* x ph ) $=
    ( wex wmo hbe1 hbmo 19.8a immoi alrimi ) ACDZBEABECKCBACFGAKBACHIJ $.
    $( [3-Dec-2001] $)

  $( Double quantification with existential uniqueness.  (The proof was
     shortened by Andrew Salmon, 9-Jul-2011.) $)
  2euex $p |- ( E! x E. y ph -> E. y E! x ph ) $=
    ( wex weu wmo wa eu5 excom hbe1 19.8a immoi df-mo sylib eximd syl5bi impcom
    hbmo wi sylbi ) ACDZBEUABDZUABFZGABEZCDZUABHUCUBUEUBABDZCDUCUEABCIUCUFUDCUA
    CBACJRUCABFUFUDSAUABACKLABMNOPQT $.
    $( [9-Jul-2011] $) $( [3-Dec-2001] $)

  $( Double quantification with existential uniqueness and "at most one." $)
  2eumo $p |- ( E! x E* y ph -> E* x E! y ph ) $=
    ( weu wmo wi euimmo eumo mpg ) ACDZACEZFKBDJBEFBJKBGACHI $.
    $( [3-Dec-2001] $)

  $( Double existential uniqueness. $)
  2eu2ex $p |- ( E! x E! y ph -> E. x E. y ph ) $=
    ( weu wex euex eximi syl ) ACDZBDIBEACEZBEIBFIJBACFGH $.
    $( [3-Dec-2001] $)

  $( A condition allowing swap of "at most one" and existential quantifiers. $)
  2moswap $p |- ( A. x E* y ph -> ( E* x E. y ph -> E* y E. x ph ) ) $=
    ( wmo wal wex wa hbe1 moexex expcom 19.8a pm4.71ri exbii mobii syl6ibr ) AC
    DBEZACFZBDZQAGZBFZCDZABFZCDRPUAQABCACHIJUBTCASBAQACKLMNO $.
    $( [10-Apr-2004] $)

  $( A condition allowing swap of uniqueness and existential quantifiers. $)
  2euswap $p |- ( A. x E* y ph -> ( E! x E. y ph -> E! y E. x ph ) ) $=
    ( wmo wal wex wa weu wi excomim a1i 2moswap anim12d eu5 3imtr4g ) ACDBEZACF
    ZBFZQBDZGABFZCFZTCDZGQBHTCHPRUASUBRUAIPABCJKABCLMQBNTCNO $.
    $( [10-Apr-2004] $)

  $( Double existential uniqueness implies double uniqueness quantification. $)
  2exeu $p |- ( ( E! x E. y ph /\ E! y E. x ph ) -> E! x E! y ph ) $=
    ( wex wmo weu excom hbe1 19.41 19.8a immoi anim2i eximi sylbir sylanb simpl
    wa hbmo eu5 anbi12i adantl anim12i ancoms exbii mobii bitri 3imtr4i ) ACDZB
    DZUHBEZQZABDZCDZULCEZQZQUHACEZQZBDZUQBEZQZUHBFZULCFZQACFZBFZUOUKUTUOURUKUSU
    MUIUNURACBGUIUNQUHUNQZBDURUHUNBULBCABHRIVEUQBUNUPUHAULCABJKLMNOUJUSUIUQUHBU
    HUPPKUAUBUCVAUKVBUOUHBSULCSTVDVCBDZVCBEZQUTVCBSVFURVGUSVCUQBACSZUDVCUQBVHUE
    TUFUG $.
    $( [3-Dec-2001] $)

  ${
    $d x y z w v u $.  $d z w v u ph $.
    $( Two equivalent expressions for double "at most one." $)
    2mo $p |- ( E. z E. w A. x A. y ( ph -> ( x = z /\ y = w ) ) <->
              A. x A. y A. z A. w ( ( ph /\ [ z / x ] [ w / y ] ph ) ->
                   ( x = z /\ y = w ) ) ) $=
      ( vv vu weq wa wi wal wex wsb equequ2 bi2anan9 ax-17 albii bitri 2alimi
      wn imbi2d 2albidv cbvex2v hbs1 hbim hbsb sbequ12 sylan9bbr equequ1 cbval2
      imbi12d biimpi ancli alcom aaan hbal sylibr prth equtr2 anim12i an4s syl6
      syl exlimivv sylbir impexp bi2.04 2albii alrimi 2eximi alrot4 alim al2imi
      sylbi exim alimi syl5com syl5bi alnex notbid biimpri pm2.21 19.8a 19.23bi
      3syl hbn a1d pm2.61i impbii ) ABDHZCEHZIZJZCKZBKZELZDLZAACEMZBDMZIZWLJZEK
      DKZCKBKZWQABFHZCGHZIZJZCKZBKZGLFLXCXIWOFGDEFDHZGEHZIZXGWMBCXLXFWLAXJXDWJX
      KXEWKFDBNGECNOUAUBUCXIXCFGXIXGWSDFHZEGHZIZJZIZEKZDKZCKZBKZXCXIXIXPEKZDKZI
      ZYAXIYCXIYCXGXPBCDEXGDPXGEPZWSXOBWRBDUDZXOBPUEZWSXOCWRBDCACEUDUFZXOCPUEZW
      LAWSXFXOWKAWRWJWSACEUGWRBDUGUHZWJXDXMWKXEXNBDFUICEGUIOUKUJULUMYAXHYBIZDKZ
      BKYDXTYLBXTXRCKZDKYLXRCDUNYMYKDXGXPCEYEYIUOQRQXHYBBDXHDPXPBEYGUPUORUQXSXB
      BCXQXADEXQWTXFXOIWLAXFWSXOURXDXMXEXNWLXDXMIWJXEXNIWKBDFUSCEGUSUTVAVBSSVCV
      DVEWSELZDLZXCWQJXCWSWMJZEKDKZCKBKZYOWQXBYQBCXAYPDEXAAWSWLJJYPAWSWLVFAWSWL
      VGRVHVHYOWSCKZBKZELZDLZYRWQWSYTDEWSYSBYFYHVIVJYRYTWOJZEKZDKZUUAWPJZDKUUBW
      QJYRYPCKZBKZEKDKUUEYPBCDEVKUUHUUCDEUUGYSWNBWSWMCVLVMSVNUUDUUFDYTWOEVOVPUU
      AWPDVOWEVQVRYOTZWQXCUUIWSTZEKZDKZWQUULYNTZDKUUIUUKUUMDWSEVSQYNDVSRUULATZC
      KBKZWOWQUUOUULUUNUUJBCDEUUNDPUUNEPWSBYFWFWSCYHWFWLAWSYJVTUJWAUUNWMBCAWLWB
      SWOWQEWPDWCWDWEVEWGWHWI $.
      $( [2-Feb-2005] $)
  $}

  ${
    $d z w ph $.  $d x y ps $.  $d x y z w $.
    2mos.1 $e |- ( ( x = z /\ y = w ) -> ( ph <-> ps ) ) $.
    $( Double "exists at most one", using implicit substitition. $)
    2mos $p |- ( E. z E. w A. x A. y ( ph -> ( x = z /\ y = w ) ) <->
             A. x A. y A. z A. w ( ( ph /\ ps ) -> ( x = z /\ y = w ) ) ) $=
      ( weq wa wi wal wex wsb 2mo ax-17 sbrim wb expcom sbie 2albii pm5.74ri
      pm5.74d bitr3i anbi2i imbi1i bitri ) ACEHZDFHZIZJDKCKFLELAADFMZCEMZIZUIJZ
      FKEKZDKCKABIZUIJZFKEKZDKCKACDEFNUNUQCDUMUPEFULUOUIUKBAUJBCEBCOUGUJBUGUJJU
      GAJZDFMUGBJZUGADFUGDOPURUSDFUSDOUHUGABUGUHABQGRUBSUCUASUDUETTUF $.
      $( [10-Feb-2005] $)
  $}

  $( Double existential uniqueness.  This theorem shows a condition under which
     a "naive" definition matches the correct one. $)
  2eu1 $p |- ( A. x E* y ph ->
        ( E! x E! y ph <-> ( E! x E. y ph /\ E! y E. x ph ) ) ) $=
    ( wmo wal weu wex wa wi eu5 exbii mobii anbi12i bitri simprbi anim2i ancoms
    ax-4 sylib com12 immoi hba1 moanim ancrd 2moswap imdistani syl 2eu2ex excom
    syl6 jca jctild an4 syl6ibr 2exeu impbid1 ) ACDZBEZACFZBFZACGZBFZABGZCFZHZU
    TURVEUTURVABGZVCCGZHZVABDZVCCDZHZHZVEUTURVKVHUTVAUQHZBDZURVKIUTVMBGZVNUTUSB
    GZUSBDZHVOVNHUSBJVPVOVQVNUSVMBACJZKUSVMBVRLMNOVNURVIURHVKVNURVIVNURVAHZBDUR
    VIIVSVMBVAURVMURUQVAUQBRPQUAURVABUQBUBUCSUDVIURVJURVIVJABCUETUFUJUGUTVFVGAB
    CUHZUTVFVGVTABCUISUKULVEVFVIHZVGVJHZHVLVBWAVDWBVABJVCCJMVFVIVGVJUMNUNTABCUO
    UP $.
    $( [3-Dec-2001] $)

  $( Double existential uniqueness. $)
  2eu2 $p |- ( E! y E. x ph -> ( E! x E! y ph <-> E! x E. y ph ) ) $=
    ( wex weu wmo wal wi eumo 2moex 2eu1 simpl syl6bi 3syl 2exeu expcom impbid
    wa ) ABDZCEZACEBEZACDBEZTSCFACFBGZUAUBHSCIACBJUCUAUBTRUBABCKUBTLMNUBTUAABCO
    PQ $.
    $( [3-Dec-2001] $)


  $( Double existential uniqueness. $)
  2eu3 $p |- ( A. x A. y ( E* x ph \/ E* y ph ) ->
 ( ( E! x E! y ph /\ E! y E! x ph ) <-> ( E! x E. y ph /\ E! y E. x ph ) ) ) $=
    ( wmo wo wal weu wa wex wb hbmo1 19.31 albii hbal 19.32 bitri wi 2eu1 2exeu
    biimpd ancom syl6ib adantld adantrd jaoi ancoms jca impbid1 sylbi ) ABDZACD
    ZECFZBFZUJCFZUKBFZEZACGBGZABGCGZHZACIBGZABICGZHZJUMUNUKEZBFUPULVCBUJUKCACKL
    MUNUKBUJBCABKNOPUPUSVBUNUSVBQUOUNURVBUQUNURVAUTHZVBUNURVDACBRTVAUTUAUBUCUOU
    QVBURUOUQVBABCRTUDUEVBUQURABCSVAUTURACBSUFUGUHUI $.
    $( [3-Dec-2001] $)

  ${
    $d x y z w $.  $d z w ph $.
    $( This theorem provides us with a definition of double existential
       uniqueness ("exactly one ` x ` and exactly one ` y ` ").  Naively one
       might think (incorrectly) that it could be defined by
       ` E! x E! y ph ` .  See ~ 2eu1 for a condition under which the naive
       definition holds and ~ 2exeu for a one-way implication.  See ~ 2eu5 and
       ~ 2eu8 for alternate definitions. $)
    2eu4 $p |- ( ( E! x E. y ph /\ E! y E. x ph ) <->
      ( E. x E. y ph /\ E. z E. w A. x A. y ( ph -> ( x = z /\ y = w ) ) ) ) $=
      ( wex weu wa weq wal ax-17 eu3 anbi12i anbi2i bitri hba1 19.3 19.26 albii
      wi an4 excom anidm jcab 3bitr4ri alcom bitr4i 19.23v 2albii 3bitri 2exbii
      hbe1 hbim aaan eeanv bitr2i ) ACFZBGZABFZCGZHUQBFZUQBDIZTZBJZDFZHZUSCFZUS
      CEIZTZCJZEFZHZHVAVGHZVEVKHZHVAAVBVHHTZCJZBJZEFDFZHURVFUTVLUQBDUQDKLUSCEUS
      EKLMVAVEVGVKUAVMVAVNVRVMVAVAHVAVGVAVAACBUBNVAUCOVRVDVJHZEFDFVNVQVSDEVQAVB
      TZCJZAVHTZBJZHZCJZBJZVCVIHZCJBJVSVQWAWBCJZBJZHZBJZWFWABJZWIBJZHWLWIHZWKVQ
      WMWIWLWIBWHBPQNWAWIBRVQWAWHHZBJWNVPWOBVPVTWBHZCJWOVOWPCAVBVHUDSVTWBCROSWA
      WHBROUEWEWJBWEWACJZWCCJZHWJWAWCCRWQWAWRWIWACVTCPQWBCBUFMOSUGWDWGBCWAVCWCV
      IAVBCUHAVHBUHMUIVCVIBCUQVBCACULVBCKUMUSVHBABULVHBKUMUNUJUKVDVJDEUOUPMUJ
      $.
      $( [3-Dec-2001] $)

    $( An alternate definition of double existential uniqueness (see ~ 2eu4 ).
       A mistake sometimes made in the literature is to use ` E! x E! y ` to
       mean "exactly one ` x ` and exactly one ` y ` ."  (For example, see
       Proposition 7.53 of [TakeutiZaring] p. 53.)  It turns out that this is
       actually a weaker assertion, as can be seen by expanding out the formal
       definitions.  This theorem shows that the erroneous definition can be
       repaired by conjoining ` A. x E* y ph ` as an additional condition.  The
       correct definition apparently has never been published.  ( ` E* ` means
       "exists at most one.") $)
    2eu5 $p |- ( ( E! x E! y ph /\ A. x E* y ph ) <->
      ( E. x E. y ph /\ E. z E. w A. x A. y ( ph -> ( x = z /\ y = w ) ) ) ) $=
      ( weu wmo wal wa wex weq 2eu1 pm5.32ri eumo adantl 2moex syl pm4.71i 2eu4
      wi 3bitr2i ) ACFBFZACGBHZIACJZBFZABJZCFZIZUCIUHUDBJABDKCEKITCHBHEJDJIUCUB
      UHABCLMUHUCUHUFCGZUCUGUIUEUFCNOACBPQRABCDESUA $.
      $( [26-Oct-2003] $)
  $}

  ${
    $d x y z w v u $.  $d z w v u ph $.
    $( Two equivalent expressions for double existential uniqueness. $)
    2eu6 $p |- ( ( E! x E. y ph /\ E! y E. x ph ) <->
               E. z E. w A. x A. y ( ph <-> ( x = z /\ y = w ) ) ) $=
      ( vu vv wex wa weq wi wal ax-17 hbsb sbequ12 equequ2 bi2anan9 hbim 2exbii
      wsb weu 2eu4 19.29r2 hbs1 sylan9bbr cbvex2 imbi2d 2albidv cbvex2v equequ1
      wb imbi12d cbval2 3bitri anbi12i 2albiim ancom bitri equcom imbi2i impexp
      2mo 2albii hban sbco2 sbcom2 sbbii 3bitr3ri syl6bb anbi2d 19.21-2 3bitr3i
      anbi2i abai 2sb6 anbi1i 3bitr2i bitr4i 3imtr4i 2alimi 2eximi 2exsb sylibr
      bi2 bi1 jca impbii ) ACHZBUAABHCUAIWHBHZABDJZCEJZIZKZCLBLZEHDHZIZAWLUKZCL
      BLZEHDHZABCDEUBWPWSACETZBDTZEHDHZXAXAEFTZDGTZIZDGJZEFJZIZKZFLGLZELDLZIXAX
      JIZEHDHZWPWSXAXJDEUCWIXBWOXKAXABCDEADMAEMZWTBDUDZWTBDCACEUDNZWKAWTWJXAACE
      OWTBDOUEZUFWOABGJZCFJZIZKZCLBLZFHGHXAXHKZELDLZFHGHXKWNYBDEGFXHWMYABCXHWLX
      TAXFWJXRXGWKXSDGBPEFCPQUGUHUIYBYDGFYAYCBCDEYADMYAEMXAXHBXOXHBMZRXAXHCXPXH
      CMZRWLAXAXTXHXQWJXRXFWKXSXGBDGUJCEFUJQULUMSXADEGFVBUNUOWSWLAKZCLBLZWNIZEH
      DHXMWRYIDEWRWNYHIYIAWLBCUPWNYHUQURSXLYIDEXLXAXAWNKZIXAWNIYIXJYJXAXAAIZDBJ
      ZECJZIZKZCLBLXAWMKZCLBLXJYJYOYPBCYOYKWLKYPYNWLYKYLWJYMWKDBUSECUSUOUTXAAWL
      VAURVCYOXIBCGFYOGMYOFMXEXHBXAXDBXOXCDGBXAEFBXONNVDYERXEXHCXAXDCXPXCDGCXAE
      FCXPNNVDYFRXTYKXEYNXHXTAXDXAXTAACFTZBGTZXDXSAYQXRYRACFOYQBGOUEWTEFTZBDTZD
      GTYSBGTXDYRYSBGDYSDMVEYTXCDGWTEFBDVFVGYSYQBGACFEXNVEVGVHVIVJXRYLXFXSYMXGB
      GDPCFEPQULUMXAWMBCXOXPVKVLVMXAWNVNXAYHWNABCDEVOVPVQSVRVSWSWIWOWSYHEHDHWIW
      RYHDEWQYGBCAWLWDVTWAABCDEWBWCWRWNDEWQWMBCAWLWEVTWAWFWGUR $.
      $( [2-Feb-2005] $)
  $}

  $( Two equivalent expressions for double existential uniqueness. $)
  2eu7 $p |- ( ( E! x E. y ph /\ E! y E. x ph ) <->
             E! x E! y ( E. x ph /\ E. y ph ) ) $=
    ( wex weu wa hbe1 hbeu euan ancom eubii 3bitri 3bitr4ri ) ABDZCEZACDZFZBEOP
    BEZFNPFZCEZBEROFOPBNBCABGHITQBTPNFZCEPOFQSUACNPJKPNCACGIPOJLKROJM $.
    $( [19-Feb-2005] $)

  $( Two equivalent expressions for double existential uniqueness.  Curiously,
     we can put ` E! ` on either of the internal conjuncts but not both.  We
     can also commute ` E! x E! y ` using ~ 2eu7 . $)
  2eu8 $p |- ( E! x E! y ( E. x ph /\ E. y ph ) <->
                E! x E! y ( E! x ph /\ E. y ph ) ) $=
    ( wex wa 2eu2 pm5.32i hbeu1 hbeu euan ancom eubii hbe1 3bitri 3bitr4ri 2eu7
    weu 3bitr3ri ) ACDZBQZABQZCQZEZTABDZCQZEUASEZCQZBQZUDSECQBQTUBUEACBFGUBSEZB
    QUBTEUHUCUBSBUABCABHIJUGUIBUGSUAEZCQSUBEUIUFUJCUASKLSUACACMJSUBKNLTUBKOABCP
    R $.
    $( [20-Feb-2005] $)

  ${
    $d x y z $.
    $( Equality has existential uniqueness.  Special case of ~ eueq1 proved
       using only predicate calculus.  (Contributed by Stefan Allan,
       4-Dec-2008.) $)
    euequ1 $p |- E! x x = y $=
      ( vz weq weu wex wa wi wal a9e equtr2 gen2 equequ1 eu4 mpbir2an ) ABDZAEP
      AFPCBDZGACDHZCIAIABJRACACBKLPQACACBMNO $.
      $( [4-Dec-2008] $)
  $}

  ${
    $d x y $.
    $( Two ways to express "only one thing exists."  The left-hand side
       requires only one variable to express this.  Both sides are false in set
       theory; see theorem ~ dtru . $)
    exists1 $p |- ( E! x x = x <-> A. x x = y ) $=
      ( weq weu wb wal wex df-eu equid tbt bicom bitri albii exbii hbae 3bitr2i
      19.9 ) AACZADRABCZEZAFZBGSAFZBGUBRABHUBUABSTASSRETRSAIJSRKLMNUBBABBOQP $.
      $( [5-Apr-2004] $)

    $( A condition implying that at least two things exist.  (The proof was
       shortened by Andrew Salmon, 9-Jul-2011.) $)
    exists2 $p |- ( ( E. x ph /\ E. x -. ph ) -> -. E! x x = x ) $=
      ( vy wex wn cv wceq weu wal hbeu1 hba1 wi exists1 ax-16 sylbi exlimd alex
      com12 syl6ib con2d imp ) ABDZAEBDZBFZUDGZBHZEUBUFUCUBUFABIZUCEUFUBUGUFAUG
      BUEBJABKUFUDCFGBIAUGLBCMABCNOPRABQSTUA $.
      $( [9-Jul-2011] $) $( [10-Apr-2004] $)
  $}

$(
###############################################################################
                PEANO ARITHMETIC
###############################################################################
$)

$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
                           Theory of definitions
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)

  $c io. $.
  $v a b c d e f g h i j k l m n o p q r s t $.
  $v A B C D E F G H I J K L M N O P Q R S T U V W X Y Z $.
  eA $f exp A $.
  eB $f exp B $.
  eC $f exp C $.
  eD $f exp D $.
  eE $f exp E $.
  eF $f exp F $.
  eG $f exp G $.
  eH $f exp H $.
  eI $f exp I $.
  eJ $f exp J $.
  eK $f exp K $.
  eL $f exp L $.
  eM $f exp M $.
  eN $f exp N $.
  eO $f exp O $.
  eP $f exp P $.
  eQ $f exp Q $.
  eR $f exp R $.
  eS $f exp S $.
  eT $f exp T $.
  eU $f exp U $.
  eV $f exp V $.
  eW $f exp W $.
  eX $f exp X $.
  eY $f exp Y $.
  eZ $f exp Z $.


  va $f set a $.
  vb $f set b $.
  vc $f set c $.
  vd $f set d $.
  ve $f set e $.
  vf $f set f $.
  vg $f set g $.
  vh $f set h $.
  vi $f set i $.
  vj $f set j $.
  vk $f set k $.
  vl $f set l $.
  vm $f set m $.
  vn $f set n $.
  vo $f set o $.
  vp $f set p $.
  vq $f set q $.
  vr $f set r $.
  vs $f set s $.
  vt $f set t $.
  $( PLEASE PUT DESCRIPTION HERE. $)
  cio $a exp ( io. x ph ) $.

  ${
    $d x A $.
    $( This expresses the fact that in yapeano.mm, unlike in set.mm, expression
       variables cannot fail to refer. $)
    ax-ex $a |- E! x x = A $.
  $}

  ${
    $d z X $.  $d z Y $.
    $( PLEASE PUT DESCRIPTION HERE. $)
    df-exeq $a |- ( X = Y <-> A. z ( z = X <-> z = Y ) ) $.
  $}

  ${
    $d X a $.  $d Y a $.  $d Z a $.
    $( PLEASE PUT DESCRIPTION HERE. $)
    eqcom $p |- ( X = Y <-> Y = X ) $=
      ( va cv wceq wb wal bicom albii df-exeq 3bitr4i ) CDZAEZLBEZFZCGNMFZCGABE
      BAEOPCMNHICABJCBAJK $.
    $( [24-Jan-2015] $)
    eqid $p |- X = X $=
      ( va wceq cv wb df-exeq biid mpgbir ) AACBDACZIEBBAAFIGH $.
      $( [24-Jan-2015] $)
    $( PLEASE PUT DESCRIPTION HERE. $)
    eqtr $p |- ( ( X = Y /\ Y = Z ) -> X = Z ) $=
      ( va cv wceq wb wal wa 19.26 bitr alimi sylbir df-exeq anbi12i 3imtr4i )
      DEZAFZQBFZGZDHZSQCFZGZDHZIZRUBGZDHZABFZBCFZIACFUETUCIZDHUGTUCDJUJUFDRSUBK
      LMUHUAUIUDDABNDBCNODACNP $.
      $( [24-Jan-2015] $)
  $}

  $( Class identity law with antecedent. $)
  eqidd $p |- ( ph -> A = A ) $=
    ( wceq eqid a1i ) BBCABDE $.
    $( [21-Aug-2008] $)

  ${
    eqcoms.1 $e |- ( A = B -> ph ) $.
    $( Inference applying commutative law for class equality to an
       antecedent. $)
    eqcoms $p |- ( B = A -> ph ) $=
      ( wceq eqcom sylbi ) CBEBCEACBFDG $.
      $( [5-Aug-1993] $)
  $}

  ${
    eqcomi.1 $e |- A = B $.
    $( Inference from commutative law for class equality. $)
    eqcomi $p |- B = A $=
      ( wceq eqcom mpbi ) ABDBADCABEF $.
      $( [5-Aug-1993] $)
  $}

  ${
    eqcomd.1 $e |- ( ph -> A = B ) $.
    $( Deduction from commutative law for class equality. $)
    eqcomd $p |- ( ph -> B = A ) $=
      ( wceq eqcom sylib ) ABCECBEDBCFG $.
      $( [15-Aug-1994] $)
  $}

  ${
    $d x A $.  $d x B $.  $d x C $.
    $( Equality implies equivalence of equalities. $)
    eqeq1 $p |- ( A = B -> ( A = C <-> B = C ) ) $=
      ( wceq eqcom eqtr sylanb impbida ) ABDZACDZBCDZIBADJKABEBACFGABCFH $.
      $( [24-Jan-2015] $)
  $}

  ${
    eqeq1i.1 $e |- A = B $.
    $( Inference from equality to equivalence of equalities. $)
    eqeq1i $p |- ( A = C <-> B = C ) $=
      ( wceq wb eqeq1 ax-mp ) ABEACEBCEFDABCGH $.
      $( [5-Aug-1993] $)
  $}

  ${
    eqeq1d.1 $e |- ( ph -> A = B ) $.
    $( Deduction from equality to equivalence of equalities. $)
    eqeq1d $p |- ( ph -> ( A = C <-> B = C ) ) $=
      ( wceq wb eqeq1 syl ) ABCFBDFCDFGEBCDHI $.
      $( [27-Dec-1993] $)
  $}

  $( Equality implies equivalence of equalities. $)
  eqeq2 $p |- ( A = B -> ( C = A <-> C = B ) ) $=
    ( wceq eqeq1 eqcom 3bitr4g ) ABDACDBCDCADCBDABCECAFCBFG $.
    $( [5-Aug-1993] $)

  ${
    eqeq2i.1 $e |- A = B $.
    $( Inference from equality to equivalence of equalities. $)
    eqeq2i $p |- ( C = A <-> C = B ) $=
      ( wceq wb eqeq2 ax-mp ) ABECAECBEFDABCGH $.
      $( [5-Aug-1993] $)
  $}

  ${
    eqeq2d.1 $e |- ( ph -> A = B ) $.
    $( Deduction from equality to equivalence of equalities. $)
    eqeq2d $p |- ( ph -> ( C = A <-> C = B ) ) $=
      ( wceq wb eqeq2 syl ) ABCFDBFDCFGEBCDHI $.
      $( [27-Dec-1993] $)
  $}

  $( Equality relationship among 4 classes. $)
  eqeq12 $p |- ( ( A = B /\ C = D ) -> ( A = C <-> B = D ) ) $=
    ( wceq eqeq1 eqeq2 sylan9bb ) ABEACEBCECDEBDEABCFCDBGH $.
    $( [3-Aug-1994] $)

  ${
    eqeq12i.1 $e |- A = B $.
    eqeq12i.2 $e |- C = D $.
    $( A useful inference for substituting definitions into an equality.  (The
       proof was shortened by Andrew Salmon, 25-May-2011.) $)
    eqeq12i $p |- ( A = C <-> B = D ) $=
      ( wceq wb eqeq12 mp2an ) ABGCDGACGBDGHEFABCDIJ $.
      $( [25-May-2011] $) $( [5-Aug-1993] $)
  $}

  ${
    eqeq12d.1 $e |- ( ph -> A = B ) $.
    eqeq12d.2 $e |- ( ph -> C = D ) $.
    $( A useful inference for substituting definitions into an equality.  (The
       proof was shortened by Andrew Salmon, 25-May-2011.) $)
    eqeq12d $p |- ( ph -> ( A = C <-> B = D ) ) $=
      ( wceq wb eqeq12 syl2anc ) ABCHDEHBDHCEHIFGBCDEJK $.
      $( [14-Jun-2011] $) $( [5-Aug-1993] $)
  $}

  ${
    eqeqan12d.1 $e |- ( ph -> A = B ) $.
    eqeqan12d.2 $e |- ( ps -> C = D ) $.
    $( A useful inference for substituting definitions into an equality.  (The
       proof was shortened by Andrew Salmon, 25-May-2011.) $)
    eqeqan12d $p |- ( ( ph /\ ps ) -> ( A = C <-> B = D ) ) $=
      ( wceq wb eqeq12 syl2an ) ACDIEFICEIDFIJBGHCDEFKL $.
      $( [25-May-2011] $) $( [9-Aug-1994] $)
  $}

  ${
    eqeqan12rd.1 $e |- ( ph -> A = B ) $.
    eqeqan12rd.2 $e |- ( ps -> C = D ) $.
    $( A useful inference for substituting definitions into an equality. $)
    eqeqan12rd $p |- ( ( ps /\ ph ) -> ( A = C <-> B = D ) ) $=
      ( wceq wb eqeqan12d ancoms ) ABCEIDFIJABCDEFGHKL $.
      $( [9-Aug-1994] $)
  $}

  $( A transitive law for class equality.  (The proof was shortened by Andrew
     Salmon, 25-May-2011.) $)
  eqtr2 $p |- ( ( A = B /\ A = C ) -> B = C ) $=
    ( wceq eqcom eqtr sylanb ) ABDBADACDBCDABEBACFG $.
    $( [25-May-2011] $) $( [20-May-2005] $)

  $( A transitive law for class equality. $)
  eqtr3 $p |- ( ( A = C /\ B = C ) -> A = B ) $=
    ( wceq eqcom eqtr sylan2b ) BCDACDCBDABDBCEACBFG $.
    $( [20-May-2005] $)

  ${
    eqtri.1 $e |- A = B $.
    eqtri.2 $e |- B = C $.
    $( An equality transitivity inference. $)
    eqtri $p |- A = C $=
      ( wceq eqeq2i mpbi ) ABFACFDBCAEGH $.
      $( [5-Aug-1993] $)
  $}

  ${
    eqtr2i.1 $e |- A = B $.
    eqtr2i.2 $e |- B = C $.
    $( An equality transitivity inference. $)
    eqtr2i $p |- C = A $=
      ( eqtri eqcomi ) ACABCDEFG $.
      $( [21-Feb-1995] $)
  $}

  ${
    eqtr3i.1 $e |- A = B $.
    eqtr3i.2 $e |- A = C $.
    $( An equality transitivity inference. $)
    eqtr3i $p |- B = C $=
      ( eqcomi eqtri ) BACABDFEG $.
      $( [6-May-1994] $)
  $}

  ${
    eqtr4i.1 $e |- A = B $.
    eqtr4i.2 $e |- C = B $.
    $( An equality transitivity inference. $)
    eqtr4i $p |- A = C $=
      ( eqcomi eqtri ) ABCDCBEFG $.
      $( [5-Aug-1993] $)
  $}

  ${
    3eqtri.1 $e |- A = B $.
    3eqtri.2 $e |- B = C $.
    3eqtri.3 $e |- C = D $.
    $( An inference from three chained equalities. $)
    3eqtri $p |- A = D $=
      ( eqtri ) ABDEBCDFGHH $.
      $( [29-Aug-1993] $)

    $( An inference from three chained equalities.  (The proof was shortened by
       Andrew Salmon, 25-May-2011.) $)
    3eqtrri $p |- D = A $=
      ( eqtri eqtr2i ) ACDABCEFHGI $.
      $( [25-May-2011] $) $( [3-Aug-2006] $)
  $}

  ${
    3eqtr2i.1 $e |- A = B $.
    3eqtr2i.2 $e |- C = B $.
    3eqtr2i.3 $e |- C = D $.
    $( An inference from three chained equalities. $)
    3eqtr2i $p |- A = D $=
      ( eqtr4i eqtri ) ACDABCEFHGI $.
      $( [3-Aug-2006] $)

    $( An inference from three chained equalities.  (The proof was shortened by
       Andrew Salmon, 25-May-2011.) $)
    3eqtr2ri $p |- D = A $=
      ( eqtr4i eqtr2i ) ACDABCEFHGI $.
      $( [3-Aug-2006] $)
  $}

  ${
    3eqtr3i.1 $e |- A = B $.
    3eqtr3i.2 $e |- A = C $.
    3eqtr3i.3 $e |- B = D $.
    $( An inference from three chained equalities.  (The proof was shortened by
       Andrew Salmon, 25-May-2011.) $)
    3eqtr3i $p |- C = D $=
      ( eqtr3i ) BCDABCEFHGH $.
      $( [25-May-2011] $) $( [6-May-1994] $)

    $( An inference from three chained equalities. $)
    3eqtr3ri $p |- D = C $=
      ( eqtr3i ) BDCGABCEFHH $.
      $( [15-Aug-2004] $)
  $}

  ${
    3eqtr4i.1 $e |- A = B $.
    3eqtr4i.2 $e |- C = A $.
    3eqtr4i.3 $e |- D = B $.
    $( An inference from three chained equalities.  (The proof was shortened by
       Andrew Salmon, 25-May-2011.) $)
    3eqtr4i $p |- C = D $=
      ( eqtr4i ) CADFDBAGEHH $.
      $( [25-May-2011] $) $( [5-Aug-1993] $)

    $( An inference from three chained equalities.  (The proof was shortened by
       Andrew Salmon, 25-May-2011.) $)
    3eqtr4ri $p |- D = C $=
      ( eqtr4i ) DACDBAGEHFH $.
      $( [25-May-2011] $) $( [2-Sep-1995] $)
  $}

  ${
    eqtrd.1 $e |- ( ph -> A = B ) $.
    eqtrd.2 $e |- ( ph -> B = C ) $.
    $( An equality transitivity deduction. $)
    eqtrd $p |- ( ph -> A = C ) $=
      ( wceq eqeq2d mpbid ) ABCGBDGEACDBFHI $.
      $( [5-Aug-1993] $)
  $}

  ${
    eqtr2d.1 $e |- ( ph -> A = B ) $.
    eqtr2d.2 $e |- ( ph -> B = C ) $.
    $( An equality transitivity deduction. $)
    eqtr2d $p |- ( ph -> C = A ) $=
      ( eqtrd eqcomd ) ABDABCDEFGH $.
      $( [18-Oct-1999] $)
  $}

  ${
    eqtr3d.1 $e |- ( ph -> A = B ) $.
    eqtr3d.2 $e |- ( ph -> A = C ) $.
    $( An equality transitivity equality deduction. $)
    eqtr3d $p |- ( ph -> B = C ) $=
      ( eqcomd eqtrd ) ACBDABCEGFH $.
      $( [18-Jul-1995] $)
  $}

  ${
    eqtr4d.1 $e |- ( ph -> A = B ) $.
    eqtr4d.2 $e |- ( ph -> C = B ) $.
    $( An equality transitivity equality deduction. $)
    eqtr4d $p |- ( ph -> A = C ) $=
      ( eqcomd eqtrd ) ABCDEADCFGH $.
      $( [18-Jul-1995] $)
  $}

  ${
    3eqtrd.1 $e |- ( ph -> A = B ) $.
    3eqtrd.2 $e |- ( ph -> B = C ) $.
    3eqtrd.3 $e |- ( ph -> C = D ) $.
    $( A deduction from three chained equalities. $)
    3eqtrd $p |- ( ph -> A = D ) $=
      ( eqtrd ) ABCEFACDEGHII $.
      $( [29-Oct-1995] $)

    $( A deduction from three chained equalities.  (The proof was shortened by
       Andrew Salmon, 25-May-2011.) $)
    3eqtrrd $p |- ( ph -> D = A ) $=
      ( eqtrd eqtr2d ) ABDEABCDFGIHJ $.
      $( [25-May-2011] $) $( [4-Aug-2006] $)
  $}

  ${
    3eqtr2d.1 $e |- ( ph -> A = B ) $.
    3eqtr2d.2 $e |- ( ph -> C = B ) $.
    3eqtr2d.3 $e |- ( ph -> C = D ) $.
    $( A deduction from three chained equalities. $)
    3eqtr2d $p |- ( ph -> A = D ) $=
      ( eqtr4d eqtrd ) ABDEABCDFGIHJ $.
      $( [4-Aug-2006] $)

    $( A deduction from three chained equalities. $)
    3eqtr2rd $p |- ( ph -> D = A ) $=
      ( eqtr4d eqtr2d ) ABDEABCDFGIHJ $.
      $( [4-Aug-2006] $)
  $}

  ${
    3eqtr3d.1 $e |- ( ph -> A = B ) $.
    3eqtr3d.2 $e |- ( ph -> A = C ) $.
    3eqtr3d.3 $e |- ( ph -> B = D ) $.
    $( A deduction from three chained equalities.  (The proof was shortened by
       Andrew Salmon, 25-May-2011.) $)
    3eqtr3d $p |- ( ph -> C = D ) $=
      ( eqtr3d ) ACDEABCDFGIHI $.
      $( [25-May-2011] $) $( [4-Aug-1995] $)

    $( A deduction from three chained equalities. $)
    3eqtr3rd $p |- ( ph -> D = C ) $=
      ( eqtr3d ) ACEDHABCDFGII $.
      $( [14-Jan-2006] $)
  $}

  ${
    3eqtr4d.1 $e |- ( ph -> A = B ) $.
    3eqtr4d.2 $e |- ( ph -> C = A ) $.
    3eqtr4d.3 $e |- ( ph -> D = B ) $.
    $( A deduction from three chained equalities.  (The proof was shortened by
       Andrew Salmon, 25-May-2011.) $)
    3eqtr4d $p |- ( ph -> C = D ) $=
      ( eqtr4d ) ADBEGAECBHFII $.
      $( [25-May-2011] $) $( [4-Aug-1995] $)

    $( A deduction from three chained equalities. $)
    3eqtr4rd $p |- ( ph -> D = C ) $=
      ( eqtr4d ) AEBDAECBHFIGI $.
      $( [21-Sep-1995] $)
  $}

  ${
    syl5eq.1 $e |- A = B $.
    syl5eq.2 $e |- ( ph -> B = C ) $.
    $( An equality transitivity deduction. $)
    syl5eq $p |- ( ph -> A = C ) $=
      ( wceq a1i eqtrd ) ABCDBCGAEHFI $.
      $( [5-Aug-1993] $)
  $}

  ${
    syl5req.1 $e |- A = B $.
    syl5req.2 $e |- ( ph -> B = C ) $.
    $( An equality transitivity deduction. $)
    syl5req $p |- ( ph -> C = A ) $=
      ( syl5eq eqcomd ) ABDABCDEFGH $.
      $( [29-Mar-1998] $)
  $}

  ${
    syl5eqr.1 $e |- B = A $.
    syl5eqr.2 $e |- ( ph -> B = C ) $.
    $( An equality transitivity deduction. $)
    syl5eqr $p |- ( ph -> A = C ) $=
      ( eqcomi syl5eq ) ABCDCBEGFH $.
      $( [5-Aug-1993] $)
  $}

  ${
    syl5reqr.1 $e |- B = A $.
    syl5reqr.2 $e |- ( ph -> B = C ) $.
    $( An equality transitivity deduction. $)
    syl5reqr $p |- ( ph -> C = A ) $=
      ( eqcomi syl5req ) ABCDCBEGFH $.
      $( [29-Mar-1998] $)
  $}

  ${
    syl6eq.1 $e |- ( ph -> A = B ) $.
    syl6eq.2 $e |- B = C $.
    $( An equality transitivity deduction. $)
    syl6eq $p |- ( ph -> A = C ) $=
      ( wceq a1i eqtrd ) ABCDECDGAFHI $.
      $( [5-Aug-1993] $)
  $}

  ${
    syl6req.1 $e |- ( ph -> A = B ) $.
    syl6req.2 $e |- B = C $.
    $( An equality transitivity deduction. $)
    syl6req $p |- ( ph -> C = A ) $=
      ( syl6eq eqcomd ) ABDABCDEFGH $.
      $( [29-Mar-1998] $)
  $}

  ${
    syl6eqr.1 $e |- ( ph -> A = B ) $.
    syl6eqr.2 $e |- C = B $.
    $( An equality transitivity deduction. $)
    syl6eqr $p |- ( ph -> A = C ) $=
      ( eqcomi syl6eq ) ABCDEDCFGH $.
      $( [5-Aug-1993] $)
  $}

  ${
    syl6reqr.1 $e |- ( ph -> A = B ) $.
    syl6reqr.2 $e |- C = B $.
    $( An equality transitivity deduction. $)
    syl6reqr $p |- ( ph -> C = A ) $=
      ( eqcomi syl6req ) ABCDEDCFGH $.
      $( [29-Mar-1998] $)
  $}

  ${
    sylan9eq.1 $e |- ( ph -> A = B ) $.
    sylan9eq.2 $e |- ( ps -> B = C ) $.
    $( An equality transitivity deduction.  (The proof was shortened by Andrew
       Salmon, 25-May-2011.) $)
    sylan9eq $p |- ( ( ph /\ ps ) -> A = C ) $=
      ( wceq eqtr syl2an ) ACDHDEHCEHBFGCDEIJ $.
      $( [25-May-2011] $) $( [8-May-1994] $)
  $}

  ${
    sylan9req.1 $e |- ( ph -> B = A ) $.
    sylan9req.2 $e |- ( ps -> B = C ) $.
    $( An equality transitivity deduction. $)
    sylan9req $p |- ( ( ph /\ ps ) -> A = C ) $=
      ( eqcomd sylan9eq ) ABCDEADCFHGI $.
      $( [23-Jun-2007] $)
  $}

  ${
    sylan9eqr.1 $e |- ( ph -> A = B ) $.
    sylan9eqr.2 $e |- ( ps -> B = C ) $.
    $( An equality transitivity deduction. $)
    sylan9eqr $p |- ( ( ps /\ ph ) -> A = C ) $=
      ( wceq sylan9eq ancoms ) ABCEHABCDEFGIJ $.
      $( [8-May-1994] $)
  $}

  ${
    3eqtr3g.1 $e |- ( ph -> A = B ) $.
    3eqtr3g.2 $e |- A = C $.
    3eqtr3g.3 $e |- B = D $.
    $( A chained equality inference, useful for converting from definitions. $)
    3eqtr3g $p |- ( ph -> C = D ) $=
      ( syl5eqr syl6eq ) ADCEADBCGFIHJ $.
      $( [15-Nov-1994] $)
  $}

  ${
    3eqtr4g.1 $e |- ( ph -> A = B ) $.
    3eqtr4g.2 $e |- C = A $.
    3eqtr4g.3 $e |- D = B $.
    $( A chained equality inference, useful for converting to definitions. $)
    3eqtr4g $p |- ( ph -> C = D ) $=
      ( syl5eq syl6eqr ) ADCEADBCGFIHJ $.
      $( [5-Aug-1993] $)
  $}

  ${
    3eqtr4a.1 $e |- A = B $.
    3eqtr4a.2 $e |- ( ph -> C = A ) $.
    3eqtr4a.3 $e |- ( ph -> D = B ) $.
    $( A chained equality inference, useful for converting to definitions.
       (The proof was shortened by Andrew Salmon, 25-May-2011.) $)
    3eqtr4a $p |- ( ph -> C = D ) $=
      ( syl6eq eqtr4d ) ADCEADBCGFIHJ $.
      $( [25-May-2011] $) $( [2-Feb-2007] $)
  $}

  ${
    eq2tr.1 $e |- ( A = C -> D = F ) $.
    eq2tr.2 $e |- ( B = D -> C = G ) $.
    $( A compound transitive inference for class equality. $)
    eq2tri $p |- ( ( A = C /\ B = F ) <-> ( B = D /\ A = G ) ) $=
      ( wceq wa ancom eqeq2d pm5.32i 3bitr3i ) ACIZBDIZJPOJOBEIZJPAFIZJOPKOPQOD
      EBGLMPORPCFAHLMN $.
      $( [22-Jan-2004] $)
  $}

  ${
    $d x y z $.  $d ph z $.
    $( Define behavior of iota.  Metalogically, this extends the definition of
       =, i.e. to eliminate this definition, transform equalities.  Fix one
       element of the domain (remember, this is not free logic); let
       ` x = ( io. y ph ) ` mean that ` x ` is the unique individual such that
       ` [ x / y ] ph ` if there is one, or else let it mean that ` x ` is the
       fixed domain element.  Iota on the RHS of equality was not valid before
       so this is conservative.  The second clause states that all wrong iotas
       are equal. $)
    df-io $a |- ( y = ( io. x ph ) <->
        ( ( E! x ph /\ A. x ( ph <-> x = y ) ) \/
          ( -. E! x ph /\ y = ( io. z F. ) ) ) ) $.

    $( There is exactly one out-of-domain value. $)
    ax-edom $a |- E! x x = ( io. y F. ) $.
  $}

  ${
    $d ph y z w $.  $d ps y z w $.  $d x y z w $.
    $( PLEASE PUT DESCRIPTION HERE. $)
    eio1 $p |- ( E! x ph -> ( y = ( io. x ph ) <-> A. x ( ph <-> x = y ) ) ) $=
      ( vz cv cio wceq weu weq wb wal wa wn wfal wo df-io ibar notnot1 intnanrd
      biorf syl orcom syl6bb bitr2d syl5bb ) CEZABFGABHZABCIJBKZLZUGMZUFNDFGZLZ
      OZUGUHABCDPUGUHUIUMUGUHQUGUIULUIOZUMUGULMUIUNJUGUJUKUGRSULUITUAULUIUBUCUD
      UE $.
    $( [24-Jan-2015] $)
    eio2 $p |- ( -. E! x ph -> ( y = ( io. x ph ) <-> y = ( io. z F. ) ) ) $=
      ( cv cio wceq weu weq wb wal wa wn wfal wo df-io ibar id1 intnanrd biorf
      syl bitr2d syl5bb ) CEZABFGABHZABCIJBKZLZUEMZUDNDFGZLZOZUHUIABCDPUHUIUJUK
      UHUIQUHUGMUJUKJUHUEUFUHRSUGUJTUAUBUC $.
    $( [24-Jan-2015] $)
    iobit $p |- ( A. x ( ph <-> ps ) -> ( io. x ph ) = ( io. x ps ) ) $=
      ( vz vw wb wal cv cio wceq weu wa weq bibi1 syl eio1 adantr biimpac eio2
      wn alimi albi adantl hba1 ax-4 eubid 3bitr4d wfal notbid bitr4d pm2.61ian
      alrimiv df-exeq sylibr ) ABFZCGZDHZACIZJZUQBCIZJZFZDGURUTJUPVBDACKZUPVBVC
      UPLZACDMZFZCGZBVEFZCGZUSVAUPVGVIFZVCUPVFVHFZCGVJUOVKCABVENUAVFVHCUBOUCVCU
      SVGFUPACDPQVDBCKZVAVIFUPVCVLUPABCUOCUDUOCUEUFZRBCDPOUGVCTZUPLZUSUQUHEIJZV
      AVNUSVPFUPACDESQVOVLTZVAVPFUPVNVQUPVCVLVMUIRBCDESOUJUKULDURUTUMUN $.
      $( [24-Jan-2015] $)
  $}

  ${
    $d ph y z w u $.  $d ps x z w u $.
    $( PLEASE PUT DESCRIPTION HERE. $)
    cbviot $p |- ( A. x A. y ( x = y -> ( ph <-> ps ) ) -> ( io. x ph ) = ( io.
        y ps ) ) $=
      ? $.
  $}
