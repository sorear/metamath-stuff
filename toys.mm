$(
=-=-=-=-
 Stuff which is NOT being used for Matiyasevich
=-=-=-=-
$)

$[ set_clean.mm $]

  ${
    $d x y A $.  $d x y B $.
    setindtr $p |- ( A. x ( x C_ A -> x e. A ) -> ( E. y ( Tr y /\ B e. y ) -> B e. A ) ) $=
      ( cv wtr wcel wa wex wss wi wal cdif c0 wceq cin wn sylib adantlr ex wrex
      wral ax-17 hba1 hban eldifn adantl wel eldifi trss syl5 df-ss sseq1d ax-4
      imp ad2antlr sylbid mtod inssdif0 sylnib ralrimi ralnex difss ssexi zfreg
      vex necon1bi syl ssdif0 sylibr simplr sseldd exlimiv com12 ) BEZFZDVOGZHZ
      BIAEZCJZVSCGZKZALZDCGZVRWCWDKBVRWCWDVRWCHVOCDVPWCVOCJZVQVPWCHZVOCMZNOZWEW
      FVSWGPNOZAWGUAZQZWHWFWIQZAWGUBWKWFWLAWGVPWCAVPAUCWBAUDUEWFVSWGGZWLWFWMHZV
      SVOPZCJZWIWNWPWAWMWAQWFVSVOCUFUGWNWPVTWAWNWOVSCVPWMWOVSOZWCVPWMHVSVOJZWQV
      PWMWRWMABUHVPWRVSVOCUIVOVSUJUKUOVSVOULRSUMWCWBVPWMWBAUNUPUQURVSVOCUSUTTVA
      WIAWGVBRWJWGNAWGWGVOBVFVOCVCVDVEVGVHVOCVIVJSVPVQWCVKVLTVMVN $.
      $( [28-Oct-2014] $)
  $}

  ${
    $d B a x z $.  $d ph y $.  $d ps x $.  $d ch x $. $d ph a z $.  $d a x y $.
    setindtrs.a $e |- ( A. y e. x ps -> ph ) $.
    setindtrs.b $e |- ( x = y -> ( ph <-> ps ) ) $.
    setindtrs.c $e |- ( x = B -> ( ph <-> ch ) ) $.
    setindtrs $p |- ( E. z ( Tr z /\ B e. z ) -> ch ) $=
      ( va cv wtr wcel wa wex wi wral hbab1 cvv cab setindtr dfss3 ax17el hbral
      wss hbim weq raleq eleq1 imbi12d vex elab ralbii abid 3imtr4i chvar sylbi
      mpg wb elex adantl exlimiv elabg syl mpbid ) FLZMZGVGNZOZFPZGADUAZNZCKLZV
      LUFZVNVLNZQVKVMQKKFVLGUBVOELZVLNZEVNRZVPEVNVLUCVREDLZRZVTVLNZQVSVPQDKVSVP
      DVRDEVNEKDUDADESUEADKSUGDKUHWAVSWBVPVREVTVNUIVTVNVLUJUKBEVTRAWAWBHVRBEVTA
      BDVQEULIUMUNADUOUPUQURUSVKGTNZVMCUTVJWCFVIWCVHGVGVAVBVCACDGTJVDVEVF $.
      $( [28-Oct-2014] $)
  $}

  ${
    $d a b c x y $.
    $d N a b c x y $.

    dford3lem1 $p |- ( ( Tr N /\ A. y e. N Tr y ) ->
        A. b e. N ( Tr b /\ A. y e. b Tr y ) ) $=
      ( wtr cv wral wa treq cbvralv biimpi adantl wcel wi wss trss ssralv com23
      syl6 imp ralrimiv r19.26 sylanbrc ) BDZAEZDZABFZGZCEZDZCBFZUEAUHFZCBFUIUK
      GCBFUFUJUCUFUJUEUIACBUDUHHIJKUGUKCBUCUFUHBLZUKMUCULUFUKUCULUHBNUFUKMBUHOU
      EAUHBPRQSTUIUKCBUAUB $.
      $( [28-Oct-2014] $)

    dford3lem2 $p |- ( ( Tr x /\ A. y e. x Tr y ) -> x e. On ) $=
      ( vc va vb cv wtr wa wral con0 wcel vex treq anbi12d wi word sylibr raleq
      weq eleq1 wel wex csuc trsuc2 sucid sucex eleq2 cla4ev sylancl adantr wss
      wceq simprl dford3lem1 ralim syl5 imp dfss3 ordon trssord syl3anc elon ex
      a1i imbi12d setindtrs mpcom ) CFZGZACUAZHZCUBZAFZGZBFGZBVMIZHZVMJKZVNVLVP
      VNVMUCZGZVMVSKZVLVMUDVMALZUEVKVTWAHCVSVMWBUFVHVSULVIVTVJWAVHVSMVHVSVMUGNU
      HUIUJDFZGZVOBWCIZHZWCJKZOEFZGZVOBWHIZHZWHJKZOZVQVRODECVMWMEWCIZWFWGWNWFHZ
      WCPZWGWOWDWCJUKZJPZWPWNWDWEUMWOWLEWCIZWQWNWFWSWFWKEWCIWNWSBWCEUNWKWLEWCUO
      UPUQEWCJURQWRWOUSVDWCJUTVAWCDLVBQVCDESZWFWKWGWLWTWDWIWEWJWCWHMVOBWCWHRNWC
      WHJTVEDASZWFVQWGVRXAWDVNWEVPWCVMMVOBWCVMRNWCVMJTVEVFVG $.
      $( [28-Oct-2014] $)

    dford3 $p |- ( Ord N <-> ( Tr N /\ A. x e. N Tr x ) ) $=
      ( va word wtr cv wral wa ordtr wcel ordelord syl ralrimiva jca con0 simpl
      wss dford3lem1 dford3lem2 ralimi dfss3 biimpri 3syl ordon trssord syl3anc
      a1i impbii ) BDZBEZAFZEZABGZHZUIUJUMBIUIULABUIUKBJHUKDULBUKKUKILMNUNUJBOQ
      ZODZUIUJUMPUNCFZEULAUQGHZCBGUQOJZCBGZUOABCRURUSCBCASTUOUTCBOUAUBUCUPUNUDU
      GBOUEUFUH $.
      $( [28-Oct-2014] $)

    dford4 $p |- ( Ord N <-> A. a A. b A. c ( ( a e. N /\ b e. a ) ->
        ( b e. N /\ ( c e. b -> c e. a ) ) ) ) $=
      ( wtr cv wa wel wi wal dftr2 ax-17 ancom imbi1i bitri 2albii alcom bitr4i
      wcel impexp word dford3 df-ral imbi2i 19.21-2 bicomi anbi2i anass 3bitr3i
      wral 19.3 3bitri albii anbi12i 19.26 19.26-2 pm4.76 bitr3i ) AUAAEZBFZEZB
      AUJZGZUTASZCBHZGZCFASZIZDJZCJZVFDCHZDBHZIZIZDJCJZGZBJZVFVGVMGIZDJCJZBJBAU
      BVCVJBJZVOBJZGVQUSVTVBWAUSVEVDGZVGIZBJCJZVTCBAKVTWCCJBJWDVIWCBCVIVHWCVHDV
      HDLUKVFWBVGVDVEMNOPWCBCQORVBVDVAIZBJWAVABAUCWEVOBWEVDVKVEGZVLIZCJDJZIZVDW
      GIZCJDJZVOVAWHVDDCUTKUDWKWIVDWGDCVDDLVDCLUEUFWKVNCJDJVOWJVNDCVDWFGZVLIVFV
      KGZVLIWJVNWLWMVLWLVDVEVKGZGWMWFWNVDVKVEMUGVDVEVKUHRNVDWFVLTVFVKVLTUIPVNDC
      QOULUMOUNVJVOBUORVPVSBVPVHVNGZDJCJVSVHVNCDUPWOVRCDVFVGVMUQPURUMUL $.
      $( [28-Oct-2014] $)
  $}

  ${
    $d ph y $.  $d x y $.  $d A y a $.
    reuen1 $p |- ( E! x e. A ph <-> { x e. A | ph } ~~ 1o ) $=
      ( vy wreu crab cv csn wceq wex c1o cen wbr reusn en1 bitr4i ) ABCEABCFZDG
      HIDJQKLMABDCNDQOP $.
      $( [28-Oct-2014] $)

    euen1 $p |- ( E! x ph <-> { x | ph } ~~ 1o ) $=
      ( cvv wreu crab c1o cen wbr weu cab reuen1 reuv rabab breq1i 3bitr3i ) AB
      CDABCEZFGHABIABJZFGHABCKABLPQFGABMNO $.
      $( [28-Oct-2014] $)

    sdom1 $p |- ( A ~< 1o <-> A = (/) ) $=
      ( va c1o csdm wbr c0 wceq wcel relsdom brrelexi cv wi breq1 eqeq1 imbi12d
      cvv wn cdom domnsym 0sdom con2i 0sdom1dom biimpi necon2bbii sylibr vtoclg
      vex nsyl mpcom wne 1n0 con0 1on elexi mpbir mpbiri impbii ) ACDEZAFGZAPHU
      RUSACDIJBKZCDEZUTFGZLURUSLBAPUTAGVAURVBUSUTACDMUTAFNOVAFUTDEZQVBVACUTREZV
      CVDVACUTSUAVCVDUTBUGZUBUCUHVCUTFUTVETUDUEUFUIUSURFCDEZVFCFUJUKCCULUMUNTUO
      AFCDMUPUQ $.
      $( [28-Oct-2014] $)

    modom $p |- ( E* x ph <-> { x | ph } ~<_ 1o ) $=
      ( wmo wex weu wi wn wo cab c1o cdom wbr df-mo imor csdm cen c0 wceq sdom1
      abn0 necon1bbii eqid1 mpbir breq1 mpbiri biimpi impbii bitri euen1 brdom2
      orbi12i bitr4i 3bitri ) ABCABDZABEZFUNGZUOHZABIZJKLZABMUNUONUQURJOLZURJPL
      ZHUSUPUTUOVAUPURQRZUTUNURQABTUAVBUTVBUTQJOLZVCQQRQUBQSUCURQJOUDUEUTVBURSU
      FUGUHABUIUKURJUJULUM $.
      $( [28-Oct-2014] $)
  $}

  $( Eight inequivalent definitions of finite sets from http://consequences.emich.edu/note-94.pdf . $)

  $c Fin1a Fin2 Fin3 Fin4 Fin5 Fin6 Fin7 $.
  cfin1a $a class Fin1a $.
  cfin2 $a class Fin2 $.
  cfin3 $a class Fin3 $.
  cfin4 $a class Fin4 $.
  cfin5 $a class Fin5 $.
  cfin6 $a class Fin6 $.
  cfin7 $a class Fin7 $.

  ${
    $d A c f a $.  $d B c f a $.
    $( An infinite set contains subsets equinumerous to every finite set.
       Extension of ~ isinf from finite ordinals to all finite sets. $)
    isinffi $p |- ( ( -. A e. Fin /\ B e. Fin ) -> E. f f : B -1-1-> A ) $=
    ( vc va cfn wcel wn wa cv wss cen wbr wex wf1 com ad2antlr syl2anc mpd ex
    ccrd cfv wral ficardom isinf wceq anbi2d exbidv rcla4va syl2anr wf1o simprr
    breq2 ficardid entr ensymg vex bren sylib f1of1 adantl simplrl f1ss exlimdv
    wi eximdv ) AFGHZBFGZIZDJZAKZVJBUAUBZLMZIZDNZBACJZOZCNZVHVLPGVKVJEJZLMZIZDN
    ZEPUCVOVGBUDDAEUEWBVOEVLPVSVLUFZWAVNDWCVTVMVKVSVLVJLUMUGUHUIUJVIVNVRDVIVNVR
    VIVNIZBVJVPUKZCNZVRWDBVJLMZWFWDVJBLMZWGWDVMVLBLMZWHVIVKVMULVHWIVGVNBUNQVJVL
    BUORVHWHWGVEVGVNVJBFUPQSBVJCDUQURUSWDWEVQCWDWEVQWDWEIBVJVPOZVKVQWEWJWDBVJVP
    UTVAVIVKVMWEVBBVJAVPVCRTVFSTVDS $.
    $( [8-Oct-2014] $)
  $}

  $( why are the arguments to ficarddom backward $)

  ${
    $d A a $.  $d B a $.
    ficardsdom $p |- ( ( A e. Fin /\ B e. Fin ) -> ( ( card ` A ) e.
      ( card ` B ) <-> A ~< B ) ) $=
      ( cfn wcel wa ccrd cfv wss wne cdom wbr wn csdm ficarddom bicomd ficarden
      cen necon3abid con0 cardon anbi12d wb onelpss mp2an brsdom 3bitr4g ) ACDB
      CDEZAFGZBFGZHZUHUIIZEZABJKZABQKZLZEUHUIDZABMKUGUJUMUKUOUGUMUJABNOUGUNUHUI
      ABPRUAUHSDUISDUPULUBATBTUHUIUCUDABUEUF $.
      $( [30-Oct-2014] $)

    fidomtri $p |- ( A e. Fin -> ( A ~<_ B <-> -. B ~< A ) ) $=
      ( va cfn wcel cdom wbr csdm wn domnsym wi ccrd cfv wss con0 cardon ancoms
      wa wb cvv ficarddom ontri1 mp2an ficardsdom notbid syl5bb biimprd wf1 wex
      bitrd cv isinffi vex f1f dmfex sylancr f1domg mpcom exlimiv syl pm2.61dan
      wf a1d impbid2 ) ADEZABFGZBAHGZIZABJVEBDEZVHVFKVEVIRZVFVHVJVFALMZBLMZNZVH
      ABUAVMVLVKEZIZVJVHVKOEVLOEVMVOSAPBPVKVLUBUCVJVNVGVIVEVNVGSBAUDQUEUFUJUGVE
      VIIZRVFVHVPVEVFVPVERABCUKZUHZCUIVFBACULVRVFCATEZVRVFVRVQTEABVQVBVSCUMABVQ
      UNABTVQUOUPABTVQUQURUSUTQVCVAVD $.
      $( [30-Oct-2014] $)
  $}

  ${
    fidomtri2.a $e |- A e. _V $.
    fidomtri2 $p |- ( B e. Fin -> ( A ~<_ B <-> -. B ~< A ) ) $=
      ( cfn wcel cdom wbr csdm wn domnsym cen wa sdomdom con3i fidomtri syl5ibr
      wi ensym endom syl a1i jcad brsdom syl6ibr con1d impbid2 ) BDEZABFGZBAHGZ
      IABJUGUHUIUGUHIZBAFGZBAKGZIZLUIUGUJUKUMUJUKUGABHGZIUNUHABMNBAOPUJUMQUGULU
      HULABKGUHBACRABSTNUAUBBAUCUDUEUF $.
      $( [30-Oct-2014] $)

    sdom2en01 $p |- ( A ~< 2o <-> ( A ~~ (/) \/ A ~~ 1o ) ) $=
      ( c2o wbr cfn wcel c0 cen c1o wo com con0 0fin ccrd cfv wceq eqeq2i mpan2
      wb syl5bbr csdm cdom cin onfin2 inss2 eqsstri 2onn sselii sdomdom sylancr
      domfi enfi mpan mpbiri 1onn jaoi csn fvex elpr df2o2 eleq2i df1o2 3bitr4i
      cpr orbi2i a1i cardnn ax-mp ficardsdom ficarden orbi12d 3bitr3d pm5.21nii
      card0 ) ACUADZAEFZAGHDZAIHDZJZVOCEFZACUBDVPKECKLEUCEUDLEUEUFZUGUHZACUICAU
      KUJVQVPVRVQVPGEFZMWCVQVPWCSMAGEULUMUNVRVPIEFZKEIWAUOUHZWDVRVPWDSWEAIEULUM
      UNUPVPANOZCFZWFGPZWFIPZJZVOVSWGWJSVPWFGGUQZVDZFWHWFWKPZJWGWJWFGWKANURUSCW
      LWFUTVAWIWMWHIWKWFVBQVEVCVFWGWFCNOZFZVPVOWNCWFCKFWNCPUGCVGVHVAVPVTWOVOSWB
      ACVIRTVPWHVQWIVRWHWFGNOZPZVPVQWPGWFVNQVPWCWQVQSMAGVJRTWIWFINOZPZVPVRWRIWF
      IKFWRIPUOIVGVHQVPWDWSVRSWEAIVJRTVKVLVM $.
      $( [30-Oct-2014] $)
  $}

  ${
    $d a b c d f x y $.
    $d ph b c d $.  $d G b c d $.
    infpssrlem.a $e |- ( ph -> x C_ a ) $.
    infpssrlem.c $e |- ( ph -> f : x -1-1-onto-> a ) $.
    infpssrlem.d $e |- ( ph -> y e. ( a \ x ) ) $.
    infpssrlem.e $e |- G = ( rec ( `' f , y ) |` om ) $.

    infpssrlem1 $p |- ( G ` (/) ) = y $=
      ( c0 cfv cv ccnv crdg com cres fveq1i cvv wcel wceq vex fr0g ax-mp eqtri
      ) KELKDMNZCMZOPQZLZUGKEUHJRUGSTUIUGUACUBUGSUFUCUDUE $.
      $( [30-Oct-2014] $)

    infpssrlem2 $p |- ( B e. om -> ( G ` suc B ) = ( `' f ` ( G ` B ) ) ) $=
      ( com wcel csuc cv ccnv crdg cres cfv fveq1i frsuc fveq2i 3eqtr4g ) DLMDN
      ZEOPZCOZQLRZSDUGSZUESUDFSDFSZUESUFDUEUAUDFUGKTUIUHUEDFUGKTUBUC $.
      $( [30-Oct-2014] $)

    infpssrlem3 $p |- ( ph -> G : om --> a ) $=
      ( vc vb com wfn cv cfv wcel c0 fveq2 eleq1d wral wf ccnv crdg cres frfnom
      fneq1i mpbir a1i csuc wceq weq infpssrlem1 wel eldifi syl syl5eqel wa wss
      cdif adantr wf1o f1ocnv f1of 3syl ffvelrn sylan infpssrlem2 syl5ibr exp3a
      sseldd finds2 com12 ralrimiv ffnfv sylanbrc ) AEMNZKOZEPZFOZQZKMUAMVTEUBV
      QAVQDOZUCZCOZUDMUEZMNWDWCUFMEWEJUGUHUIAWAKMVRMQAWAWAREPZVTQLOZEPZVTQZWGUJ
      ZEPZVTQZAKLVRRUKVSWFVTVRRESTKLULVSWHVTVRWGESTVRWJUKVSWKVTVRWJESTAWFWDVTAB
      CDEFGHIJUMAWDVTBOZUTQCFUNIWDVTWMUOUPUQWGMQZAWIWLAWIURZWLWNWHWCPZVTQWOWMVT
      WPAWMVTUSWIGVAAVTWMWCUBZWIWPWMQAWMVTWBVBVTWMWCVBWQHWMVTWBVCVTWMWCVDVEVTWM
      WHWCVFVGVKWNWKWPVTABCWGDEFGHIJVHTVIVJVLVMVNKMVTEVOVP $.
      $( [30-Oct-2014] $)

    $d B b c $.  $d C b c $.
    infpssrlem4 $p |- ( ( ph /\ B e. om /\ C e. B ) -> ( G ` B ) =/= ( G ` C ) ) $=
      ( vb com wcel cfv wne wa wi wceq vc vd cv wral c0 fveq2 neeq1d raleqbi1dv
      csuc imbi2d weq ral0 a1i w3a ccnv infpssrlem2 adantr wel wf1o f1ocnv f1of
      wn 3syl adantl infpssrlem3 ffvelrn sylan ancoms syl2anc eldifn syl nelne2
      cdif eqnetrd 3adant3 infpssrlem1 syl6eq neeq2d syl5ibr adantrd wrex simpr
      wf peano2 elnn 3ad2antl1 simpl nnsuc ax-17 hbra1 hb3an hban word wb nnord
      simpl3 ordsucelsuc mpbird adantrr ra4 wf1 f1of1 ad2antlr adantll syl12anc
      sylc necon3bid biimprd neeq12d adantlr sylibrd adantrl 3adantl3 mpd eleq1
      f1fveq anbi2d imbi12d mpbiri com3l rexlimd ex pm2.61ine ralrimiva cbvralv
      expr sylib 3exp a2d finds impcom rcla4cv 3impia ) ADNOZEDOZDGPZEGPZQZAYNR
      YPMUCZGPZQZMDUDZYOYRSYNAUUBAUAUCZGPZYTQZMUUCUDZSAUEGPZYTQZMUEUDZSAUBUCZGP
      ZYTQZMUUJUDZSAUUJUIZGPZYTQZMUUNUDZSAUUBSUAUBDUUCUETZUUFUUIAUUEUUHMUUCUEUU
      RUUDUUGYTUUCUEGUFZUGUHUJUAUBUKZUUFUUMAUUEUULMUUCUUJUUTUUDUUKYTUUCUUJGUFUG
      UHUJUUCUUNTZUUFUUQAUUEUUPMUUCUUNUVAUUDUUOYTUUCUUNGUFUGUHUJUUCDTZUUFUUBAUU
      EUUAMUUCDUVBUUDYPYTUUCDGUFUGUHUJUUIAUUHMULUMUUJNOZAUUMUUQUVCAUUMUUQUVCAUU
      MUNZUUOUUDQZUAUUNUDUUQUVDUVEUAUUNUVDUUCUUNOZRZUVESUUCUEUURUVDUVEUVFUVDUVE
      UURUUOCUCZQZUVCAUVIUUMUVCARZUUOUUKFUCZUOZPZUVHUVCUUOUVMTZAABCUUJFGHIJKLUP
      ZUQUVJUVMBUCZOZCBURVBZUVMUVHQUVJHUCZUVPUVLWCZUUKUVSOZUVQAUVTUVCAUVPUVSUVK
      USZUVSUVPUVLUSZUVTJUVPUVSUVKUTZUVSUVPUVLVAVCVDAUVCUWAANUVSGWCZUVCUWAABCFG
      HIJKLVEZNUVSUUJGVFVGVHZUVSUVPUUKUVLVFVIAUVRUVCAUVHUVSUVPVMOUVRKUVHUVSUVPV
      JVKVDUVMUVHUVPVLVIVNVOUURUUDUVHUUOUURUUDUUGUVHUUSABCFGHIJKLVPVQVRVSVTUUCU
      EQZUVGUVEUWHUVGRZUUCYSUIZTZMNWAZUVEUWIUUCNOZUWHUWLUVGUWMUWHUVCAUVFUWMUUMU
      VCUVFRUVFUUNNOZUWMUVCUVFWBUVCUWNUVFUUJWDUQUUCUUNWEVIWFVDUWHUVGWGMUUCWHVIU
      VGUWLUVESUWHUVGUWKUVEMNUVDUVFMUVCAUUMMUVCMWIAMWIUULMUUJWJWKUVFMWIWLUVEMWI
      UWKUVGYSNOZUVEUWKUVGUWOUVESZSUVDUWJUUNOZRZUWOUUOUWJGPZQZSZSUVDUWQUWOUWTUV
      DUWQUWORZRZUULUWTUXCUUMMUBURZUULUVCAUUMUXBWPUVDUWQUXDUWOUVCAUWQUXDUUMUVCU
      WQRZUXDUWQUVCUWQWBUXEUUJWMZUXDUWQWNUVCUXFUWQUUJWOUQYSUUJWQVKWRWFWSUULMUUJ
      WTXFUVCAUXBUULUWTSZUUMUVJUWOUXGUWQUVJUWORZUULUVMYTUVLPZQZUWTUXHUXJUULUXHU
      VMUXIUUKYTUXHUVSUVPUVLXAZUWAYTUVSOZUVMUXITUUKYTTWNAUXKUVCUWOAUWBUWCUXKJUW
      DUVSUVPUVLXBVCXCUVJUWAUWOUWGUQAUWOUXLUVCAUWEUWOUXLUWFNUVSYSGVFVGXDUVSUVPU
      UKYTUVLXPXEXGXHUVCUWOUWTUXJWNAUVCUWORUUOUVMUWSUXIUVCUVNUWOUVOUQUWOUWSUXIT
      UVCABCYSFGHIJKLUPVDXIXJXKXLXMXNYFUWKUVGUWRUWPUXAUWKUVFUWQUVDUUCUWJUUNXOXQ
      UWKUVEUWTUWOUWKUUDUWSUUOUUCUWJGUFVRUJXRXSXTYAVDXNYBYCYDUVEUUPUAMUUNUAMUKU
      UDYTUUOUUCYSGUFVRYEYGYHYIYJYKUUAYRMEDYSETYTYQYPYSEGUFVRYLVKYM $.
      $( [30-Oct-2014] $)

    infpssrlem5 $p |- ( ph -> om ~<_ a ) $=
      ( vb vc com cv cfv wi wral wcel wa wel wf1 cdom wbr wf weq infpssrlem3 wo
      wceq wn simpll simplrr simpr infpssrlem4 syl3anc necomd simplrl jaodan ex
      wne necon2bd wb word nnord ordtri3 syl2an adantl sylibrd ralrimivva dff13
      sylanbrc cvv vex f1dom2g ax-mp syl ) AMFNZEUAZMVPUBUCZAMVPEUDKNZEOZLNZEOZ
      UHZKLUEZPZLMQKMQVQABCDEFGHIJUFAWEKLMMAVSMRZWAMRZSZSZWCKLTZLKTZUGZUIZWDWIW
      LVTWBWIWLVTWBUSZWIWJWNWKWIWJSZWBVTWOAWGWJWBVTUSAWHWJUJAWFWGWJUKWIWJULABCW
      AVSDEFGHIJUMUNUOWIWKSAWFWKWNAWHWKUJAWFWGWKUPWIWKULABCVSWADEFGHIJUMUNUQURU
      TWHWDWMVAZAWFVSVBWAVBWPWGVSVCWAVCVSWAVDVEVFVGVHKLMVPEVIVJVPVKRVQVRPFVLMVP
      VKEVMVNVO $.
      $( [30-Oct-2014] $)
  $}

  ${
    $d a x c y f A $.  $d a x c y f X $.
    infpssr.a $e |- A e. _V $.
    $( Dedekind infinity implies existance of a denumerable subset: take a
       single point witnessing the proper subset relation and iterate the
       embedding.  The hypothesis is technically redundant with our current
       ~ df-op . $)
    infpssr $p |- ( ( X C. A /\ X ~~ A ) -> om ~<_ A ) $=
      ( va vx vy vf cv wpss cen wbr wa com cdom wi wceq breq2 anbi12d cvv wcel
      psseq2 imbi12d relen brrelexi psseq1 imbi1d wel wn wex pssnel adantr cdif
      breq1 eldif wss pssss wf1o bren ccnv crdg simplr simpr simpll infpssrlem5
      vex cres eqid ex exlimdv syl5bi imp3a sylbir exlimiv mpcom vtoclg anabsi7
      syl5 syl vtocl ) BDHZIZBVTJKZLZMVTNKZOZBAIZBAJKZLZMANKZODACVTAPZWCWHWDWIW
      JWAWFWBWGVTABUAVTABJQRVTAMNQUBWAWBWDWBBSTWEBVTJUCUDEHZVTIZWKVTJKZLZWDOZWE
      EBSWKBPZWNWCWDWPWLWAWMWBWKBVTUEWKBVTJUMRUFFDUGFEUGUHLZFUIZWNWDWLWRWMFWKVT
      UJUKWQWOFWQFHZVTWKULTZWOWSVTWKUNWTWLWMWDWLWKVTUOZWTWMWDOZWKVTUPWTXAXBWMWK
      VTGHZUQZGUIWTXALZWDWKVTGDVEURXEXDWDGXEXDWDXEXDLEFGXCUSWSUTMVFZDWTXAXDVAXE
      XDVBWTXAXDVCXFVGVDVHVIVJVHVQVKVLVMVNVOVRVPVS $.
      $( [30-Oct-2014] $)
  $}

  ${
    $d F a b $.  $d A a b $.  $d B a b $.  $d C a b $.  $d D a b $.

    f1imass $p |- ( ( F : A -1-1-> B /\ ( C C_ A /\ D C_ A ) ) ->
      ( ( F " C ) C_ ( F " D ) <-> C C_ D ) ) $=
      ( va wf1 wss wa cima cv wcel wi simplrl sseld wb 3expa f1elima syl3anc ex
      simplr simplll simpr simp1rl simp1rr 3imtr3d pm2.43d ssrdv imass2 impbid1
      cfv syld ) ABEGZCAHZDAHZIZIZECJZEDJZHZCDHZUQUTVAUQUTIZFCDVBFKZCLZVCDLZVBV
      DVCALZVDVEMZVBCAVCUMUNUOUTNOVBVFVGVBVFIZVCEUKZURLZVIUSLZVDVEVHURUSVIUQUTV
      FUAOVHUMVFUNVJVDPUMUPUTVFUBZVBVFUCZUQUTVFUNUNUOUMUTVFUDQABEVCCRSVHUMVFUOV
      KVEPVLVMUQUTVFUOUNUOUMUTVFUEQABEVCDRSUFTULUGUHTCDEUIUJ $.
      $( [30-Oct-2014] $)

    f1imaeq $p |- ( ( F : A -1-1-> B /\ ( C C_ A /\ D C_ A ) ) ->
      ( ( F " C ) = ( F " D ) <-> C = D ) ) $=
      ( wf1 wss wa cima wceq f1imass wb ancom2s anbi12d eqss 3bitr4g ) ABEFZCAG
      ZDAGZHHZECIZEDIZGZUBUAGZHCDGZDCGZHUAUBJCDJTUCUEUDUFABCDEKQSRUDUFLABDCEKMN
      UAUBOCDOP $.
      $( [30-Oct-2014] $)

    f1imapss $p |- ( ( F : A -1-1-> B /\ ( C C_ A /\ D C_ A ) ) ->
      ( ( F " C ) C. ( F " D ) <-> C C. D ) ) $=
      ( wf1 wss wa cima wceq wpss f1imass f1imaeq notbid anbi12d dfpss2 3bitr4g
      wn ) ABEFCAGDAGHHZECIZEDIZGZTUAJZRZHCDGZCDJZRZHTUAKCDKSUBUEUDUGABCDELSUCU
      FABCDEMNOTUAPCDPQ $.
      $( [30-Oct-2014] $)
  $}

  ${
    $d A x y f a b c $.  $d B x y f a b c $.

    infpssen1 $p |- ( ( A ~~ B /\ B e. _V ) -> ( E. x ( x C. A /\ x ~~ A ) ->
      E. y ( y C. B /\ y ~~ B ) ) ) $=
      ( vb vf cen wbr cvv wcel wa cv wpss wex wi wceq breq2 anbi12d vex cima va
      relen brrelexi breq1 psseq2 exbidv imbi1d imbi12d wf1o bren simpr wf1 wss
      imbi2d wb f1of1 pssss ssid jctir f1imapss syl2an mpbird cdm imadmrn f1odm
      imaeq2d dff1o5 simprbi eqeq12d mpbii adantr psseq2d mpbid adantrr f1imaen
      crn simprr entr syl2anc f1oen2g mpan imaexg psseq1 cla4ev exlimdv exlimiv
      ax-mp ex sylbi vtocl2g adantrd sylan pm2.43i ) CDGHZDIJZKZALZCMZWQCGHZKZA
      NZBLZDMZXBDGHZKZBNZOZWNCIJZWOWPXGOCDGUBUCXHWOKWNXGWOUALZELZGHZWQXIMZWQXIG
      HZKZANZXBXJMZXBXJGHZKZBNZOZOCXJGHZXAXSOZOWNXGOUAECDIIXICPZXKYAXTYBXICXJGU
      DYCXOXAXSYCXNWTAYCXLWRXMWSXICWQUEXICWQGQRUFUGUHXJDPZYAWNYBXGXJDCGQYDXSXFX
      AYDXRXEBYDXPXCXQXDXJDXBUEXJDXBGQRUFUNUHXKXIXJFLZUIZFNXTXIXJFESUJYFXTFYFXN
      XSAYFXNXSYFXNKZYEWQTZXJMZYHXJGHZXSYFXLYIXMYFXLKZYHYEXITZMZYIYKYMXLYFXLUKY
      FXIXJYEULZWQXIUMZXIXIUMZKYMXLUOXLXIXJYEUPZXLYOYPWQXIUQZXIURUSXIXJWQXIYEUT
      VAVBYKYLXJYHYFYLXJPZXLYFYEYEVCZTZYEVPZPYSYEVDYFUUAYLUUBXJYFYTXIYEXIXJYEVE
      VFYFYNUUBXJPXIXJYEVGVHVIVJVKVLVMVNYGYHXIGHZXKYJYGYHWQGHZXMUUCYFXLUUDXMYFY
      NYOUUDXLYQYRXIXJWQYEASVOVAVNYFXLXMVQYHWQXIVRVSYFXKXNYEIJZYFXKFSZXIXJIYEVT
      WAVKYHXIXJVRVSXRYIYJKBYHUUEYHIJUUFYEWQIWBWGXBYHPXPYIXQYJXBYHXJWCXBYHXJGUD
      RWDVSWHWEWFWIWJWKWLWM $.
      $( [30-Oct-2014] $)

    infpssss $p |- ( ( A C_ B /\ B e. _V ) -> ( E. x ( x C. A /\ x ~~ A ) ->
      E. y ( y C. B /\ y ~~ B ) ) ) $=
      ( va vb vc wss cvv wcel wa cv wpss cen wbr wex wi wceq anbi12d wn imbi12d
      ssexg sseq1 psseq2 breq2 exbidv imbi1d sseq2 imbi2d psssstr pssssd ancoms
      cdif cun difss a1i unssd pssnel adantl simpll simprl sseldd simprr elndif
      wel ad2antrl wo ioran elun xchnxbir sylanbrc nelneq2 syl2anc eqcom sylnib
      ex exlimdv mpd dfpss2 adantrr cin c0 vex difexg ax-mp enref jctir ssinss1
      pssss inssdif0 sylib disjdif unen undif biimpi adantr breqtrd unex psseq1
      syl breq1 cla4ev vtocl2g adantrd sylancom pm2.43i ) CDHZDIJZKZALZCMZXJCNO
      ZKZAPZBLZDMZXODNOZKZBPZQZXGXHCIJZXIXTQCDIUBYAXHKXGXTXHELZFLZHZXJYBMZXJYBN
      OZKZAPZXOYCMZXOYCNOZKZBPZQZQCYCHZXNYLQZQXGXTQEFCDIIYBCRZYDYNYMYOYBCYCUCYP
      YHXNYLYPYGXMAYPYEXKYFXLYBCXJUDYBCXJNUESUFUGUAYCDRZYNXGYOXTYCDCUHYQYLXSXNY
      QYKXRBYQYIXPYJXQYCDXOUDYCDXONUESUFUIUAYDYGYLAYDYGYLYDYGKZXJYCYBUMZUNZYCMZ
      YTYCNOZYLYDYEUUAYFYDYEKZYTYCHYTYCRZTZUUAUUCXJYSYCYEYDXJYCHYEYDKXJYCXJYBYC
      UJUKULYSYCHUUCYCYBUOUPUQUUCGEVEZGAVEZTZKZGPZUUEYEUUJYDGXJYBURUSUUCUUIUUEG
      UUCUUIUUEUUCUUIKZYCYTRZUUDUUKGFVEGLZYTJZTZUULTUUKYBYCUUMYDYEUUIUTUUCUUFUU
      HVAVBUUKUUHUUMYSJZTZUUOUUCUUFUUHVCUUFUUQUUCUUHUUMYBYCVDVFUUGUUPVGUUHUUQKU
      UNUUGUUPVHUUMXJYSVIVJVKUUMYCYTVLVMYCYTVNVOVPVQVRYTYCVSVKVTYRYTYBYSUNZYCNY
      RYFYSYSNOZKXJYSWAWBRZYBYSWAWBRZKYTUURNOYRYFUUSYDYEYFVCYSYCIJYSIJFWCYCYBIW
      DWEZWFWGYRUUTUVAYRXJYCWAYBHZUUTYRXJYBHZUVCYEUVDYDYFXJYBWIVFXJYCYBWHWTXJYC
      YBWJWKYBYCWLWGXJYBYSYSWMVMYDUURYCRZYGYDUVEYBYCWNWOWPWQYKUUAUUBKBYTXJYSAWC
      UVBWRXOYTRYIUUAYJUUBXOYTYCWSXOYTYCNXASXBVMVPVQXCXDXEXF $.
      $( [30-Oct-2014] $)

    infpssom $p |- ( om e. _V -> E. x ( x C. om /\ x ~~ om ) ) $=
      ( va vb com cvv wcel c0 wpss cen wbr wa cv csuc wi word syl con0 a1i wceq
      syl5ibrcom csn cdif wex difexg cuni eldifi wss peano2 ordom ordelss nnord
      mpan orduniss wb orduni vex uniex elon sylibr ordsssuc syl2anc sseldd wne
      mpbid peano3 eldifsn ordunisuc eqcomd adantl unieq eqeq2d wrex nnsuc nnon
      sylanbrc suceloni eleq1 imp simpr onsucuni2 ex rexlimiv sylbi adantr en3d
      suceq impbid peano1 cin wn disjsn con2bii disj4 bitr4i jctil psseq1 breq1
      mpbi anbi12d cla4egv sylc ) DEFZDGUAZUBZEFXDDHZXDDIJZKZALZDHZXHDIJZKZAUCD
      XCEUDZXBXFXEXBBCXDDBLZUEZCLZMZXLXMXDFZXNDFZNXBXQXMDFZXRXMDXCUFXSXMMZDXNXS
      XTDFZXTDUGZXMUHDOYAYBUIDXTUJULPXSXNXMUGZXNXTFZXSXMOZYCXMUKZXMUMPXSXNQFZYE
      YCYDUNXSXNOZYGXSYEYHYFXMUOPXNXMBUPUQURUSYFXNXMUTVAVDVBPRXODFZXPXDFZNXBYIX
      PDFXPGVCYJXOUHXOVEXPDGVFVORXQYIKZXMXPSZXOXNSZUNNXBYKYLYMYKYMYLXOXPUEZSZYI
      YOXQYIYNXOYIXOOYNXOSXOUKXOVGPVHVIYLXNYNXOXMXPVJVKTYKYLYMXMXNMZSZXQYQYIXQX
      SXMGVCKZYQXMDGVFYRYLCDVLYQCXMVMYLYQCDYIYLYQYIYLKZYPXMYSXMQFZYLYPXMSYIYLYT
      YIYTYLXPQFZYIXOQFUUAXOVNXOVPPXMXPQVQTVRYIYLVSXMXOVTVAVHWAWBPWCWDYMXPYPXMX
      OXNWFVKTWGRWEGDFZXEWHUUBDXCWIGSZWJXEUUCUUBDGWKWLUUCXEDXCWMWLWNWRWOXKXGAXD
      EXHXDSXIXEXJXFXHXDDWPXHXDDIWQWSWTXA $.
      $( [30-Oct-2014] $)

    infpssALT.a $e |- A e. _V $.
    infpssALT $p |- ( om ~<_ A -> E. x ( x C. A /\ x ~~ A ) ) $=
      ( va vb vc com cdom wbr cv cen wss wa wex wpss domen cvv wcel wi mpd syl
      relen brrelexi infpssom vex infpssen1 mpan2 adantr simpr infpssss sylancl
      exlimiv sylbi ) GBHIGDJZKIZUNBLZMZDNAJZBOURBKIMANZDGBCPUQUSDUQEJZUNOUTUNK
      IMENZUSUOVAUPUOFJZGOVBGKIMFNZVAUOGQRVCGUNKUBUCFUDUAUOUNQRVCVASDUEFEGUNUFU
      GTUHUQUPBQRVAUSSUOUPUICEAUNBUJUKTULUM $.
      $( [30-Oct-2014] $)
  $}

  ${
    $d x y z a b c d $.
    $( A set is Ia-finite iff it is not the union of two I-infinite sets. $)
    df-fin1a $a |- Fin1a = { x | -. E. y E. z ( ( x = ( y u. z ) /\
      ( y i^i z ) = (/) ) /\ ( -. y e. Fin /\ -. z e. Fin ) ) } $.

    $( A set is II-finite (Tarski finite) iff every nonempty chain of subsets
       contains a maximum element. $)
    df-fin2 $a |- Fin2 = { x | A. y e. ~P ~P x ( ( y =/= (/) /\
      A. z e. y A. w e. y ( z C_ w \/ w C_ z ) ) ->
        E. z e. y A. w e. y -. z C. w ) } $.

    $( A set is IV-finite (Dedekind finite) iff it has no equinumerous proper
       subset. $)
    df-fin4 $a |- Fin4 = { x | -. E. y ( y C. x /\ y ~~ x ) } $.

    $( A set is III-finite iff its power set is Dedekind finite. $)
    df-fin3 $a |- Fin3 = { x | ~P x e. Fin4 } $.

    $( A set is V-finite iff it behaves finitely under ` +c ` . $)
    df-fin5 $a |- Fin5 = { x | ( x ~~ (/) \/ x ~< ( x +c x ) ) } $.

    $( A set is VI-finite iff it behaves finitely under ` X. ` . $)
    df-fin6 $a |- Fin6 = { x | ( x ~~ (/) \/ x ~~ 1o \/ x ~< ( x X. x ) ) } $.

    $( A set is VII-finite iff it cannot be infinitely well ordered. $)
    df-fin7 $a |- Fin7 = { x | -. E. y e. ( On \ om ) x ~~ y } $.
  $}

  ${
    $d Y z w u v $.

    fin23lem4 $p |- ( A. z e. Y A. w e. Y ( z C_ w \/ w C_ z ) ->
      ( E. u e. Y A. v e. Y -. u C. v <-> U. Y e. Y ) ) $=
      ( cv wss wo wral wpss wn wrex wcel wa weq sseq1 sseq2 orbi12d syl elssuni
      cuni w3a wi rcla42va ancoms anassrs sspss orel1 eqimss2 syl6com ax-1 jaoi
      sylbi ralimdva 3impia unissb sylibr 3ad2ant2 eqssd simp2 eqeltrd rexlimdv
      3exp ssnpss rgen wceq psseq1 notbid ralbidv rcla4ev mpan2 impbid1 ) AFZBF
      ZGZVNVMGZHZBEIAEIZDFZCFZJZKZCEIZDELZEUAZEMZVRWCWFDEVRVSEMZWCWFVRWGWCUBZWE
      VSEWHWEVSWHVTVSGZCEIZWEVSGVRWGWCWJVRWGNZWBWICEWKVTEMZNVSVTGZWIHZWBWIUCZVR
      WGWLWNWGWLNVRWNVQWNVSVNGZVNVSGZHABVSVTEEADOVOWPVPWQVMVSVNPVMVSVNQRBCOWPWM
      WQWIVNVTVSQVNVTVSPRUDUEUFWMWOWIWMWADCOZHZWOVSVTUGWBWSWRWIWAWRUHVTVSUIUJUM
      WIWBUKULSUNUOCEVSUPUQWGVRVSWEGWCVSETURUSVRWGWCUTVAVCVBWFWEVTJZKZCEIZWDXAC
      EWLVTWEGXAVTETVTWEVDSVEWCXBDWEEVSWEVFZWBXACEXCWAWTVSWEVTVGVHVIVJVKVL $.
      $( [31-Oct-2014] $)

    fin23lem5 $p |- ( A. z e. Y A. w e. Y ( z C_ w \/ w C_ z ) ->
      ( E. u e. Y A. v e. Y -. v C. u <-> |^| Y e. Y ) ) $=
      ( cv wss wo wral wpss wn wrex wcel intss1 wa weq sseq1 sseq2 orbi12d syl
      cint 3ad2ant2 wi rcla42va ancoms anassrs ax-1 sspss orel1 eqimss2 syl6com
      sylbi jaoi ralimdva 3impia ssint sylibr eqssd simp2 eqeltrd 3exp rexlimdv
      w3a ssnpss rgen wceq psseq2 notbid ralbidv rcla4ev mpan2 impbid1 ) AFZBFZ
      GZVNVMGZHZBEIAEIZCFZDFZJZKZCEIZDELZEUAZEMZVRWCWFDEVRVTEMZWCWFVRWGWCVCZWEV
      TEWHWEVTWGVRWEVTGWCVTENUBWHVTVSGZCEIZVTWEGVRWGWCWJVRWGOZWBWICEWKVSEMZOWIV
      SVTGZHZWBWIUCZVRWGWLWNWGWLOVRWNVQWNVTVNGZVNVTGZHABVTVSEEADPVOWPVPWQVMVTVN
      QVMVTVNRSBCPWPWIWQWMVNVSVTRVNVSVTQSUDUEUFWIWOWMWIWBUGWMWACDPZHZWOVSVTUHWB
      WSWRWIWAWRUIVTVSUJUKULUMTUNUOCVTEUPUQURVRWGWCUSUTVAVBWFVSWEJZKZCEIZWDXACE
      WLWEVSGXAVSENWEVSVDTVEWCXBDWEEVTWEVFZWBXACEXCWAWTVTWEVSVGVHVIVJVKVL $.
      $( [31-Oct-2014] $)
  $}

  ${
    $d Y z w b c $.  $d Y x y $.  $d Y d $.  $d d A b c $.  $d A x y b c $.
    $d Y u $.  $d A u $.  $d d u x y $.
    fin23lem6 $p |- ( A. z e. Y A. w e. Y ( z C_ w \/ w C_ z ) ->
      A. x e. { u e. ~P A | ( A \ u ) e. Y }
        A. y e. { u e. ~P A | ( A \ u ) e. Y } ( x C_ y \/ y C_ x ) ) $=
      ( vb vc vd cv wss wo wral cdif wcel wa weq wceq sseq1 difeq2 eleq1d elrab
      cpw crab an4 biimpi syl2anb wi sseq2 orbi12d rcla42v vex elpw dfss4 bitri
      sscon sseq12 syl5ib ancoms orim12d com12 orcoms syl6 com3l syl5 ralrimivv
      wb imp3a cbvral2v cbvrabv raleq raleqbi1dv ax-mp 3imtr4i ) HKZIKZLZVQVPLZ
      MZIGNHGNZAKZBKZLZWCWBLZMZBFJKZOZGPZJFUDZUEZNZAWKNZCKZDKZLZWOWNLZMZDGNCGNW
      FBFEKZOZGPZEWJUEZNZAXBNZWAWFABWKWKWBWKPZWCWKPZQWBWJPZWCWJPZQZFWBOZGPZFWCO
      ZGPZQZQZWAWFXEXGXKQZXHXMQZXOXFWIXKJWBWJJARWHXJGWGWBFUAUBUCWIXMJWCWJJBRWHX
      LGWGWCFUAUBUCXPXQQXOXGXKXHXMUFUGUHWAXIXNWFXNWAXIWFXNWAXJXLLZXLXJLZMZXIWFU
      IZVTXTXJVQLZVQXJLZMHIXJXLGGVPXJSVRYBVSYCVPXJVQTVPXJVQUJUKVQXLSYBXRYCXSVQX
      LXJUJVQXLXJTUKULXSXRYAXIXSXRMZWFXGFXJOZWBSZFXLOZWCSZYDWFUIXHXGWBFLYFWBFAU
      MUNWBFUOUPXHWCFLYHWCFBUMUNWCFUOUPYFYHQZXSWDXRWEXSYEYGLYIWDXLXJFUQYEWBYGWC
      URUSXRYGYELZYIWEXJXLFUQYHYFYJWEVHYGWCYEWBURUTUSVAUHVBVCVDVEVIVFVGWRVTVPWO
      LZWOVPLZMCDHIGGCHRWPYKWQYLWNVPWOTWNVPWOUJUKDIRYKVRYLVSWOVQVPUJWOVQVPTUKVJ
      XBWKSXDWMVHXAWIEJWJEJRWTWHGWSWGFUAUBVKXCWLAXBWKWFBXBWKVLVMVNVO $.
      $( [31-Oct-2014] $)
  $}

  ${
    $d a b c d e v u w x y z $.

    fin23lem7 $p |- ( ( b e. ~P ~P a /\ b =/= (/) ) ->
      { c e. ~P a | ( a \ c ) e. b } =/= (/) ) $=
      ( vx cv cpw wcel c0 wne cdif crab wel wex n0 wss difss elpw2 wceq sylib
      wa vex mpbir elpwi sselda dfss4 simpr eqeltrd difeq2 eleq1d sylanbrc ne0i
      a1i elrab syl ex exlimdv syl5bi imp ) BEZAEZFZFGZUSHIZUTCEZJZUSGZCVAKZHIZ
      VCDBLZDMVBVHDUSNVBVIVHDVBVIVHVBVITZUTDEZJZVGGZVHVJVLVAGZUTVLJZUSGZVMVNVJV
      NVLUTOUTVKPVLUTAUAZQUBULVJVOVKUSVJVKUTOZVOVKRVJVKVAGVRVBUSVAVKUSVAUCUDVKU
      TVQQSVKUTUESVBVIUFUGVFVPCVLVAVDVLRVEVOUSVDVLUTUHUIUMUJVGVLUKUNUOUPUQUR $.
      $( [31-Oct-2014] $)

    fin23lem8 $p |- ( ( A C_ C /\ B C_ C ) ->
      ( ( C \ A ) C. B <-> ( C \ B ) C. A ) ) $=
      ( wss wa cdif wpss difcom a1i ssconb ancoms notbid anbi12d dfpss3 3bitr4g
      wn wb ) ACDZBCDZEZCAFZBDZBUADZPZECBFZADZAUEDZPZEUABGUEAGTUBUFUDUHUBUFQTCA
      BHITUCUGSRUCUGQBACJKLMUABNUEANO $.
      $( [31-Oct-2014] $)

    fin23lem9 $p |- ( ( A C_ C /\ B C_ C ) ->
      ( B C. ( C \ A ) <-> A C. ( C \ B ) ) ) $=
      ( wss wa cdif wpss ssconb ancoms difcom a1i notbid anbi12d dfpss3 3bitr4g
      wn wb ) ACDZBCDZEZBCAFZDZUABDZPZEACBFZDZUEADZPZEBUAGAUEGTUBUFUDUHSRUBUFQB
      ACHITUCUGUCUGQTCABJKLMBUANAUENO $.
      $( [31-Oct-2014] $)

    ${
      $d ph u v x y $.  $d ps u v x y $.

      fin23lem11.a $e |- ( ( x C_ a /\ v C_ a ) -> ( [ ( a \ x ) / z ]
        [ v / w ] ps -> [ x / z ] [ ( a \ v ) / w ] ph ) ) $.

      fin23lem11 $p |- ( b e. ~P ~P a -> ( E. z e. { c e. ~P a | ( a \ c ) e. b }
        A. w e. { c e. ~P a | ( a \ c ) e. b } -. ph ->
          E. z e. b A. w e. b -. ps ) ) $=
        ( vy vu cv wcel wsb wn wral wa notbid ax-17 cpw cdif crab wi weq difeq2
        wrex eleq1d elrab w3a wsbc wel wss difss vex elpw2 mpbir a1i wceq elpwi
        simp2r sselda syl dfss4 sylib simpr eqeltrd 3ad2antl1 simpl3 cvv dfsbcq
        sylanbrc sbcbidv mpan2 rcla4va syl2anc simplrl con3d 3adantl3 ralrimiva
        adantlr mpd ralbidv rcla4ev 3exp syl5bi rexlimdv hbs1 hbn hbral sbequ12
        wb cbvral syl5bb cbvrex 3imtr4g ) HMZGMZUAZUANZAEKOZDCOZPZKWRIMZUBZWQNZ
        IWSUCZQZCXGUGBEFOZDLOZPZFWQQZLWQUGZAPZEXGQZDXGUGBPZEWQQZDWQUGWTXHXMCXGC
        MZXGNXRWSNZWRXRUBZWQNZRZWTXHXMUDXFYAIXRWSICUEXEXTWQXDXRWRUFUHUIWTYBXHXM
        WTYBXHUJZYAXIDXTUKZPZFWQQZXMWTXSYAXHVAYCYEFWQYCFHULZRZAEWRFMZUBZUKZDCOZ
        PZYEYHYJXGNZXHYMWTYBYGYNXHWTYGRZYJWSNZWRYJUBZWQNZYNYPYOYPYJWRUMWRYIUNYJ
        WRGUOZUPUQURYOYQYIWQYOYIWRUMZYQYIUSYOYIWSNZYTWTWQWSYIWQWSUTVBZYIWRUTVCY
        IWRVDVEWTYGVFVGXFYRIYJWSXDYJUSXEYQWQXDYJWRUFUHUIVLVHWTYBXHYGVIXCYMKYJXG
        KMZYJUSZXBYLUUDXRVJNXBYLWLCUOUUDXAYKDXRVJAEUUCYJVKVMVNSVOVPWTYBYGYMYEUD
        XHWTYBRYGRZYDYLUUEXRWRUMZYTYDYLUDUUEXSUUFWTXSYAYGVQXRWRUTVCUUEUUAYTWTYG
        UUAYBUUBWAYIWRYSUPVEJVPVRVSWBVTXLYFLXTWQLMZXTUSZXKYEFWQUUHXJYDXIDUUGXTV
        KSWCWDVPWEWFWGXOXHDCXGXOCTXCDKXGUUCXGNDTXBDXADCWHWIWJXOXAPZKXGQDCUEZXHX
        NUUIEKXGXNKTXAEAEKWHWIEKUEAXAAEKWKSWMUUJUUIXCKXGUUJXAXBXADCWKSWCWNWOXQX
        LDLWQXQLTXKDFWQYGDTXJDXIDLWHWIWJXQXIPZFWQQDLUEZXLXPUUKEFWQXPFTXIEBEFWHW
        IEFUEBXIBEFWKSWMUULUUKXKFWQUULXIXJXIDLWKSWCWNWOWP $.
        $( [31-Oct-2014] $)
    $}
  $}

  ${
    $d x y z w a b c d $.

    $( ` Fin2 ` expressed in terms of minimal elements. $)
    dffin2-2 $p |- Fin2 = { x | A. y e. ~P ~P x ( ( y =/= (/) /\
      A. z e. y A. w e. y ( z C_ w \/ w C_ z ) ) ->
        E. z e. y A. w e. y -. w C. z ) } $=
      ( va vb vc cv c0 wne wss wral wa wpss wrex wi cpw wcel wceq cvv cfin2 cab
      wo wn w3a cdif crab simp2 ssrab2 vex pwex elpw2 mpbir a1i simp1 fin23lem7
      simp3l syl2anc fin23lem6 adantl neeq1 raleq raleqbi1dv anbi12d rexeqbi1dv
      3ad2ant3 imbi12d rcla4va imp syl22anc wsb wsbc fin23lem9 biimpd ax-mp weq
      difexg simpr simpl psseq12d sbc2ie 3imtr4g fin23lem11 sylc 3exp fin23lem8
      ralrimiv impbii df-fin2 abeq2i pweq pweqd raleqdv elab 3bitr4i eqriv ) EU
      ABHZIJZCHZDHZKWTWSKUCZDWQLZCWQLZMZWTWSNZUDZDWQLZCWQOZPZBAHZQZQZLZAUBZFHZI
      JZXADXOLZCXOLZMZWSWTNZUDZDXOLZCXOOZPZFEHZQZQZLZXIBYGLZYEUARYEXNRYHYIYHXIB
      YGYHWQYGRZXDXHYHYJXDUEZYJYADYEGHUFZWQRZGYFUGZLZCYNOZXHYHYJXDUHZYKYNYGRZYH
      YNIJZXADYNLZCYNLZYPYRYKYRYNYFKYMGYFUIYNYFYEEUJZUKZULUMUNYHYJXDUOYKYJWRYSY
      QYHYJWRXCUQEBGUPURXDYHUUAYJXCUUAWRCDCDGYEWQUSUTVFYRYHMYSUUAMZYPYDUUDYPPFY
      NYGXOYNSZXSUUDYCYPUUEXPYSXRUUAXOYNIVAXQYTCXOYNXADXOYNVBVCVDYBYOCXOYNYADXO
      YNVBVEVGVHVIVJXTXEACDFEBGXJYEKZXOYEKMZXOYEXJUFZNZXJYEXOUFZNZXEDFVKCUUHVLX
      TDUUJVLCAVKUUGUUIUUKXJXOYEVMVNXEUUICDUUHXOYETRZUUHTRUUBYEXJTVQVOZFUJWSUUH
      SZDFVPZMWTXOWSUUHUUNUUOVRUUNUUOVSVTWAXTUUKCDXJUUJAUJZUULUUJTRUUBYEXOTVQVO
      CAVPZWTUUJSZMWSXJWTUUJUUQUURVSUUQUURVRVTWAWBWCWDWEWGYIYDFYGYIXOYGRZXSYCYI
      UUSXSUEZUUSXFDYLXORZGYFUGZLZCUVBOZYCYIUUSXSUHZUUTUVBYGRZYIUVBIJZXADUVBLZC
      UVBLZUVDUVFUUTUVFUVBYFKUVAGYFUIUVBYFUUCULUMUNYIUUSXSUOUUTUUSXPUVGUVEYIUUS
      XPXRUQEFGUPURXSYIUVIUUSXRUVIXPCDCDGYEXOUSUTVFUVFYIMUVGUVIMZUVDXIUVJUVDPBU
      VBYGWQUVBSZXDUVJXHUVDUVKWRUVGXCUVIWQUVBIVAXBUVHCWQUVBXADWQUVBVBVCVDXGUVCC
      WQUVBXFDWQUVBVBVEVGVHVIVJXEXTACDBEFGUUFWQYEKMZUUHWQNZYEWQUFZXJNZXTDBVKCUU
      HVLXEDUVNVLCAVKUVLUVMUVOXJWQYEWFVNXTUVMCDUUHWQUUMBUJUUNDBVPZMWSUUHWTWQUUN
      UVPVSUUNUVPVRVTWAXEUVOCDXJUVNUUPUULUVNTRUUBYEWQTVQVOUUQWTUVNSZMWTUVNWSXJU
      UQUVQVRUUQUVQVSVTWAWBWCWDWEWGWHYHEUAEFCDWIWJXMYIAYEUUBAEVPZXIBXLYGUVRXKYF
      XJYEWKWLWMWNWOWP $.
      $( [31-Oct-2014] $)

    dffin2-3 $p |- Fin2 = { x | A. y e. ~P ~P x ( ( y =/= (/) /\
      A. z e. y A. w e. y ( z C_ w \/ w C_ z ) ) -> U. y e. y ) } $=
      ( va vb cfin2 cv c0 wne wss wo wral wcel wi cpw weq sseq1 sseq2 orbi12d
      wa cuni cab wpss wn wrex cbvral2v fin23lem4 adantl pm5.74i ralbii df-fin2
      wb sylbi abeq2i vex pweq pweqd raleqdv elab 3bitr4i eqriv ) EGBHZIJZCHZDH
      ZKZVFVEKZLZDVCMCVCMZUAZVCUBVCNZOZBAHZPZPZMZAUCZVKVEVFUDUEDVCMCVCUFZOZBEHZ
      PZPZMZVMBWCMZWAGNWAVRNVTVMBWCVKVSVLVJVSVLUMZVDVJWAFHZKZWGWAKZLZFVCMEVCMWF
      VIWJWAVFKZVFWAKZLCDEFVCVCCEQVGWKVHWLVEWAVFRVEWAVFSTDFQWKWHWLWIVFWGWASVFWG
      WARTUGEFDCVCUHUNUIUJUKWDEGEBCDULUOVQWEAWAEUPAEQZVMBVPWCWMVOWBVNWAUQURUSUT
      VAVB $.
      $( [1-Nov-2014] $)

    dffin2-4 $p |- Fin2 = { x | A. y e. ~P ~P x ( ( y =/= (/) /\
      A. z e. y A. w e. y ( z C_ w \/ w C_ z ) ) -> |^| y e. y ) } $=
      ( va vb cfin2 cv c0 wne wss wo wral wcel wi cpw weq sseq1 sseq2 orbi12d
      wa cint cab wpss wn wrex cbvral2v fin23lem5 sylbi adantl pm5.74i dffin2-2
      wb ralbii abeq2i vex pweq pweqd raleqdv elab 3bitr4i eqriv ) EGBHZIJZCHZD
      HZKZVFVEKZLZDVCMCVCMZUAZVCUBVCNZOZBAHZPZPZMZAUCZVKVFVEUDUEDVCMCVCUFZOZBEH
      ZPZPZMZVMBWCMZWAGNWAVRNVTVMBWCVKVSVLVJVSVLUMZVDVJWAFHZKZWGWAKZLZFVCMEVCMW
      FVIWJWAVFKZVFWAKZLCDEFVCVCCEQVGWKVHWLVEWAVFRVEWAVFSTDFQWKWHWLWIVFWGWASVFW
      GWARTUGEFDCVCUHUIUJUKUNWDEGEBCDULUOVQWEAWAEUPAEQZVMBVPWCWMVOWBVNWAUQURUSU
      TVAVB $.
      $( [1-Nov-2014] $)

  $}

  $c seqom $.

  ${
    cseqom $a class seqom ( F , I ) $.

    $d F i v $.  $d I i v $.

    df-seqom $a |- seqom ( F , I ) = ( rec ( ( i e. om , v e. _V |->
        <. suc i , ( i F v ) >. ) , <. (/) , ( _I ` I ) >. ) " om ) $.
  $}

  ${
    $d F a b c d $.  $d I a b c d $.

    seqomlem0 $p |- rec ( ( a e. om , b e. _V |-> <. suc a , ( a F b ) >. ) ,
      <. (/) , ( _I ` I ) >. ) = rec ( ( c e. om , d e. _V |->
      <. suc c , ( c F d ) >. ) , <. (/) , ( _I ` I ) >. ) $=
      ( com cvv cv csuc co cop cmpt2 wceq c0 cid cfv crdg weq suceq oveq1 oveq2
      opeq12d opeq2d cbvmpt2v rdgeq1 ax-mp ) CDGHCIZJZUHDIZAKZLZMZEFGHEIZJZUNFI
      ZAKZLZMZNUMOBPQLZRUSUTRNCDEFGHULURUOUNUJAKZLCESUIUOUKVAUHUNTUHUNUJAUAUCDF
      SVAUQUOUJUPUNAUBUDUEUTUMUSUFUG $.
      $( [1-Nov-2014] $)
  $}

  ${
    $d Q a b c i v $.  $d A a b i v $.  $d F a b i v $.  $d I a b $.
    seqomlem.a $e |- Q = rec ( ( i e. om , v e. _V |->
        <. suc i , ( i F v ) >. ) , <. (/) , ( _I ` I ) >. ) $.

    seqomlem1 $p |- ( A e. om -> ( Q ` A ) =
      <. A , ( 2nd ` ( Q ` A ) ) >. ) $=
      ( vb cv cfv c2nd cop wceq c0 fveq2 id fveq2d opeq12d eqeq12d opeq2d va co
      csuc weq cid com cvv cmpt2 crdg fveq1i opex rdg0 eqtri fvex eqcomi opeq2i
      0ex op2nd 3eqtr4a ax-mp wcel df-ov suceq oveq1 oveq2 ovmpt2 mpan2 syl5eqr
      eqid eqeq1d syl5ibrcom vex sucex ovex a1i syld con0 rdgsuc fveq2i 3eqtr4g
      nnon syl sylibrd finds ) UAIZCJZWEWFKJZLZMNCJZNWIKJZLZMZHIZCJZWMWNKJZLZMZ
      WMUCZCJZWRWSKJZLZMZBCJZBXCKJZLZMUAHBWENMZWFWIWHWKWENCOZXFWENWGWJXFPXFWFWI
      KXGQRSUAHUDZWFWNWHWPWEWMCOZXHWEWMWGWOXHPXHWFWNKXIQRSWEWRMZWFWSWHXAWEWRCOZ
      XJWEWRWGWTXJPXJWFWSKXKQRSWEBMZWFXCWHXEWEBCOZXLWEBWGXDXLPXLWFXCKXMQRSWINFU
      EJZLZMZWLWINDAUFUGDIZUCZXQAIZEUBZLZUHZXOUIZJXONCYCGUJXOYBNXNUKULUMXPXONXO
      KJZLWIWKXNYDNYDXNNXNUQFUEUNURUOUPXPPXPWJYDNWIXOKOTUSUTWMUFVAZWQWNYBJZWRYF
      KJZLZMZXBYEWQYFWRWMWOEUBZLZMZYIYEYLWQWPYBJZYKMYEYMWMWOYBUBZYKWMWOYBVBYEWO
      UGVAYNYKMWNKUNDAWMWOUFUGYAYKYBWRWMXSEUBZLDHUDXRWRXTYOXQWMVCXQWMXSEVDRXSWO
      MYOYJWRXSWOWMEVETYBVIWRYJUKVFVGVHWQYFYMYKWNWPYBOVJVKYEYIYLYKWRYKKJZLZMYEY
      JYPWRYJYPMYEYPYJWRYJWMHVLVMWMWOEVNURUOVOTYLYFYKYHYQYLPYLYGYPWRYFYKKOTSVKV
      PYEWSYFXAYHYEWRYCJZWMYCJZYBJZWSYFYEWMVQVAYRYTMWMWAXOWMYBVRWBWRCYCGUJWNYSY
      BWMCYCGUJVSVTZYEWTYGWRYEWSYFKUUAQTSWCWD $.
      $( [1-Nov-2014] $)

    seqomlem2 $p |- ( Q " om ) Fn om $=
      ( va vb vc com wfn cvv cv wcel cfv wceq con0 wb cop c2nd cima cxp wss wbr
      wf weu wral dff3 wrex csuc co cmpt2 c0 crdg rdgfnon fneq1i mpbir fvelimab
      cid omsson mp2an seqomlem1 opelxpi mpan2 eqeltrd eleq1 syl5ibcom rexlimiv
      fvex sylbi ssriv weq wal wex df-br bitri wa adantl eqeq1d biimpd vex syl6
      opth1 fveq2 op2nd syl6req rexlimdva rcla4ev mpdan opeq2 eqeq2d syl5ibrcom
      rexbidv impbid syl5bb alrimiv eqeq2 bibi2d albidv cla4ev syl df-eu sylibr
      syli rgen mpbir2an dffn2 ) BJUAZJKJLXHUEZXIXHJLUBZUCGMZHMZXHUDZHUFZGJUGGH
      JLXHUHGXHXJXKXHNZXLBOZXKPZHJUIZXKXJNZBQKZJQUCZXOXRRXTCAJLCMZUJYBAMDUKSULZ
      UMEUSOSZUNZQKYDYCUOQBYEFUPUQZUTHQJXKBURVAXQXSHJXLJNZXPXJNXQXSYGXPXLXPTOZS
      ZXJAXLBCDEFVBYGYHLNYIXJNXPTVIXLYHJLVCVDVEXPXKXJVFVGVHVJVKXNGJXKJNZXMHIVLZ
      RZHVMZIVNZXNYJXMXLXKBOZTOZPZRZHVMZYNYJYRHXMIMZBOZXKXLSZPZIJUIZYJYQXMUUBXH
      NZUUDXKXLXHVOXTYAUUEUUDRYFUTIQJUUBBURVAVPYJUUDYQYJUUCYQIJYJYTJNZVQZUUCYOU
      UBPZYQUUCUUGIGVLZUUHUUGUUCYTUUATOZSZUUBPZUUIUUGUUCUULUUGUUAUUKUUBUUFUUAUU
      KPYJAYTBCDEFVBVRVSVTYTUUJXKXLIWAWCWBUUIUUCUUHUUIUUAYOUUBYTXKBWDZVSVTXDUUH
      YPUUBTOXLYOUUBTWDXKXLGWAHWAWEWFWBWGYJUUDYQUUAXKYPSZPZIJUIZYJYOUUNPZUUPAXK
      BCDEFVBUUOUUQIXKJUUIUUAYOUUNUUMVSWHWIYQUUCUUOIJYQUUBUUNUUAXLYPXKWJWKWMWLW
      NWOWPYMYSIYPYOTVIYTYPPZYLYRHUURYKYQXMYTYPXLWQWRWSWTXAXMHIXBXCXEXFJXHXGUQ
      $.
      $( [1-Nov-2014] $)

    seqomlem3 $p |- ( ( Q " om ) ` (/) ) = ( _I ` I ) $=
      ( va c0 com cfv cid wceq cop wcel cv peano1 mp2an con0 wfn mpbir cima wbr
      wrex cvv csuc co cmpt2 crdg fveq1i opex eqtri fveq2 eqeq1d rcla4ev wss wb
      rdg0 rdgfnon fneq1i omsson fvelimab df-br seqomlem2 fvex fnbrfvb ) HBIUAZ
      JEKJZLZHVGVFUBZVIHVGMZVFNZVKGOZBJZVJLZGIUCZHINZHBJZVJLZVOPVQHCAIUDCOZUEVS
      AODUFMUGZVJUHZJVJHBWAFUIVJVTHVGUJUQUKVNVRGHIVLHLVMVQVJVLHBULUMUNQBRSZIRUO
      VKVOUPWBWARSVJVTURRBWAFUSTUTGRIVJBVAQTHVGVFVBTVFISVPVHVIUPABCDEFVCPIHVGVF
      EKVDVEQT $.
      $( [1-Nov-2014] $)

    seqomlem4 $p |- ( A e. om -> ( ( Q " om ) ` suc A ) =
      ( A F ( ( Q " om ) ` A ) ) ) $=
      ( va com wcel cfv co wceq cop cv cvv con0 wfn wb sylibr csuc peano2 cmpt2
      cima wbr wrex c2nd c0 cid crdg rdgsuc syl fveq1i fveq2i 3eqtr4g seqomlem1
      nnon fveq2d df-ov fvex suceq oveq1 opeq12d oveq2 opeq2d eqid ovmpt2 mpan2
      fveq2 eqeq1d rcla4ev mpdan wss rdgfnon fneq1i mpbir omsson fvelimab mp2an
      df-br seqomlem2 fnbrfvb mpbird eqcomd oveq2d eqtrd syl5eqr 3eqtrd syl2anc
      opex mpan ovex sylancr ) BIJZBUAZCIUDZKBBWPKZELZMZWOWRWPUEZWNWOWRNZWPJZWT
      WNHOZCKZXAMZHIUFZXBWNWOIJZWOCKZXAMZXFBUBZWNXHBCKZDAIPDOZUAZXLAOZELZNZUCZK
      ZBXKUGKZNZXQKZXAWNWOXQUHFUIKNZUJZKZBYCKZXQKZXHXRWNBQJYDYFMBUQYBBXQUKULWOC
      YCGUMXKYEXQBCYCGUMUNUOWNXKXTXQABCDEFGUPZURWNYABXSXQLZXABXSXQUSWNYHWOBXSEL
      ZNZXAWNXSPJYHYJMXKUGUTZDABXSIPXPYJXQWOBXNELZNXLBMXMWOXOYLXLBVAXLBXNEVBVCX
      NXSMYLYIWOXNXSBEVDVEXQVFWOYIWJVGVHWNYIWRWOWNXSWQBEWNWQXSWNWQXSMZBXSWPUEZW
      NXTWPJZYNWNXDXTMZHIUFZYOWNXKXTMZYQYGYPYRHBIXCBMXDXKXTXCBCVIVJVKVLCQRZIQVM
      ZYOYQSYSYCQRYBXQVNQCYCGVOVPZVQHQIXTCVRVSTBXSWPVTTWPIRZWNYMYNSACDEFGWAZIBX
      SWPYKWBWKWCWDWEVEWFWGWHXEXIHWOIXCWOMXDXHXAXCWOCVIVJVKWIYSYTXBXFSUUAVQHQIX
      ACVRVSTWOWRWPVTTWNUUBXGWSWTSUUCXJIWOWRWPBWQEWLWBWMWC $.
      $( [1-Nov-2014] $)
  $}

  ${
    $d A a b $.  $d B a b $.  $d C a b $.  $d D a b $.
    seqomeq12 $p |- ( ( A = B /\ C = D ) -> seqom ( A , C ) =
      seqom ( B , D ) ) $=
      ( va vb wceq com cvv cv co cop cmpt2 c0 cid cfv crdg cima cseqom wcel wa
      csuc oveq opeq2d 3ad2ant1 mpt2eq3dva fveq2 rdgeq12 syl2an imaeq1d 3eqtr4g
      df-seqom ) ABGZCDGZUAZEFHIEJZUBZUPFJZAKZLZMZNCOPZLZQZHREFHIUQUPURBKZLZMZN
      DOPZLZQZHRACSBDSUOVDVJHUMVAVGGVCVIGVDVJGUNUMEFHIUTVFUMUPHTUTVFGURITUMUSVE
      UQUPURABUCUDUEUFUNVBVHNCDOUGUDVCVIVAVGUHUIUJFEACULFEBDULUK $.
      $( [1-Nov-2014] $)
  $}

  ${
    $d F a b c d $.  $d I a b c d $.  $d G a b c d $.  $d A a b c d $.
    seqom.a $e |- G = seqom ( F , I ) $.

    fnseqom $p |- G Fn om $=
      ( va vb vd vc com wfn cvv cv csuc co cop cmpt2 c0 cid cfv crdg cima eqtri
      seqomlem0 seqomlem2 cseqom df-seqom fneq1i mpbir ) BIJEFIKELZMUIFLANOPQCR
      SOTZIUAZIJGUJHACACEFHGUCUDIBUKBACUEUKDFEACUFUBUGUH $.
      $( [1-Nov-2014] $)

    seqom0g $p |- ( I e. _V -> ( G ` (/) ) = I ) $=
      ( va vb vd vc cvv wcel c0 cfv cid com cv csuc co cop cmpt2 eqtri df-seqom
      crdg cima cseqom fveq1i seqomlem0 seqomlem3 fvi syl5eq ) CIJKBLZCMLZCUJKE
      FNIEOZPULFOAQRSKUKRUBZNUCZLUKKBUNBACUDUNDFEACUATUEGUMHACACEFHGUFUGTCIUHUI
      $.
      $( [1-Nov-2014] $)

    seqomsuc $p |- ( A e. om -> ( G ` suc A ) = ( A F ( G ` A ) ) ) $=
      ( va vb vd vc com wcel csuc cvv cv co cop cmpt2 cfv wceq fveq1i crdg cima
      c0 cid seqomlem0 seqomlem4 cseqom df-seqom eqtri oveq2i eqeq12i sylibr )
      AJKALZFGJMFNZLUNGNBOPQUCDUDRPUAZJUBZRZAAUPRZBOZSUMCRZAACRZBOZSHAUOIBDBDFG
      IHUEUFUTUQVBUSUMCUPCBDUGUPEGFBDUHUIZTVAURABACUPVCTUJUKUL $.
      $( [1-Nov-2014] $)
  $}

  ${
    $d A x y $.  $d B x y $.  $d C x y $.  $d D x y $.
    fin23lem24 $p |- ( ( ( Ord A /\ B C_ A ) /\ ( C e. B /\ D e. B ) ) ->
      ( ( C i^i B ) = ( D i^i B ) <-> C = D ) ) $=
      ( word wa wcel cin wceq wne sseldd ordelord syl2anc simpr sylanbrc adantr
      wn elin ordirr syl wss wo simpll simplr simprl ordtri3 necon2abid simplrl
      wb simprr inss1 sseli nsyl nelne1 necomd simplrr ex sylbird necon4d ineq1
      jaodan impbid1 ) AEZBAUAZFZCBGZDBGZFZFZCBHZDBHZICDIVICDVJVKVICDJZCDGZDCGZ
      UBZVJVKJZVICEZDEZVOVLUIVIVCCAGVQVCVDVHUCZVIBACVCVDVHUDZVEVFVGUEKACLMZVIVC
      DAGVRVSVIBADVTVEVFVGUJKADLMZVQVRFVOCDCDUFUGMVIVOVPVIVMVPVNVIVMFZVKVJWCCVK
      GZCVJGZQVKVJJWCVMVFWDVIVMNVEVFVGVMUHCDBROWCCCGZWEWCVQWFQVIVQVMWAPCSTVJCCC
      BUKULUMCVKVJUNMUOVIVNFZDVJGZDVKGZQVPWGVNVGWHVIVNNVEVFVGVNUPDCBROWGDDGZWIW
      GVRWJQVIVRVNWBPDSTVKDDDBUKULUMDVJVKUNMVAUQURUSCDBUTVB $.
      $( [1-Nov-2014] $)

    fin23lem25 $p |- ( ( A e. Fin /\ B e. Fin /\ ( A C_ B \/ B C_ A ) ) ->
      ( A ~~ B <-> A = B ) ) $=
      ( cfn wcel wss cen wbr wceq wn wi wa wpss dfpss2 csdm php3 sdomnen syl ex
      syl5bir exp3a wo w3a adantl eqcom notbii anbi2i bitri cvv brrelexi ensymg
      relsdom mtod adantr jaod 3impia con4d eqeng 3ad2ant1 impbid ) ACDZBCDZABE
      ZBAEZUAZUBZABFGZABHZVEVGVFUTVAVDVGIZVFIZJZUTVAKZVBVJVCVKVBVHVIVAVBVHKZVIJ
      UTVLABLZVAVIABMVAVMVIVAVMKABNGVIBAOABPQRSUCTVKVCVHVIUTVCVHKZVIJVAVNBALZUT
      VIVOVCBAHZIZKVNBAMVQVHVCVPVGBAUDUEUFUGUTVOVIUTVOKBANGZVIABOVRVFBAFGZBAPVR
      BUHDVFVSJBANUKUIABUHUJQULQRSUMTUNUOUPUTVAVGVFJVDABCUQURUS $.
      $( [1-Nov-2014] $)
  $}

  ${
    $d i j a b c $.  $d S i j a b c $.  $d C a b c $.

    fin23lem26 $p |- ( ( ( S C_ om /\ -. S e. Fin ) /\ i e. om ) ->
      E. j e. S ( j i^i S ) ~~ i ) $=
      ( va vb cv com wcel wss cfn wn wa cin cen wbr wrex c0 wceq con0 syl breq2
      csuc rexbidv weq word ordom simpl 0fin eleq1 mpbiri necon3bi adantl tz7.5
      wne a1i syl3anc en0 incom eqeq1i bitri rexbii sylibr wi cdif cint simplrl
      difss omsson syl6ss syl5ss simplr ssel2 onfin2 eqsstri peano2 sseldi ssfi
      inss2 adantlr ex mtod ssdif0 necon3bbii sylib ad2ant2lr onint syl2anc csn
      cun simprr cvv vex en2sn mp2an simprl sseldd nnord wel ordirr inss1 sseli
      nsyl disjsn ad2antrr unen syl22anc wb ordsuc w3a simp2 simpl1 simpr eldif
      adantrr sylanbrc onnmin ee12an con4d imp simp3 sscon intss simpl2 ordelon
      ordsucss onmindif impbida df-suc eleq2i syl6bb expr pm5.32rd elin 3bitr4g
      sylan eqrdv indir syl6eq ineq1 breq1d snssi df-ss uneq2d ad2antrl 3brtr4d
      eqtrd rcla4ev rexlimdva cbvrexv syl6ib finds2 impcom ) BFZGHAGIZAJHZKZLZC
      FZAMZUUMNOZCAPZUVAUUSQNOZCAPZUUSDFZNOZCAPZUUSUVDUBZNOZCAPZUUQBDUUMQRUUTUV
      BCAUUMQUUSNUAUCBDUDUUTUVECAUUMUVDUUSNUAUCUUMUVGRUUTUVHCAUUMUVGUUSNUAUCUUQ
      AUURMZQRZCAPZUVCUUQGUEZUUNAQUNZUVLUVMUUQUFUOUUNUUPUGUUPUVNUUNUUOAQAQRUUOQ
      JHUHAQJUIUJUKULCGAUMUPUVBUVKCAUVBUUSQRUVKUUSUQUUSUVJQUURAURUSUTVAVBUVDGHZ
      UUQUVFUVIVCUVOUUQLZUVFEFZAMZUVGNOZEAPZUVIUVPUVEUVTCAUVPUURAHZUVEUVTUVPUWA
      UVELZLZAUURUBZVDZVEZAHUWFAMZUVGNOZUVTUWCUWEAUWFAUWDVGZUWCUWESIZUWEQUNZUWF
      UWEHUWCUWEASUWIUWCAGSUVOUUNUUPUWBVFZVHVIVJUUQUWAUWKUVOUVEUUQUWALZAUWDIZKU
      WKUWMUWNUUOUUNUUPUWAVKUWMUWDJHZUWNUUOVCUUNUWAUWOUUPUUNUWALUURGHZUWOAGUURV
      LUWPGJUWDGSJMJVMSJVRVNUURVOVPTVSUWOUWNUUOUWDAVQVTTWAUWNUWEQAUWDWBWCWDWEUW
      EWFWGVPUWCUUSUURWHZWIZUVDUVDWHZWIZUWGUVGNUWCUVEUWQUWSNOZUUSUWQMQRZUVDUWSM
      QRZUWRUWTNOUVPUWAUVEWJUXAUWCUURWKHUVDWKHUXACWLDWLUURUVDWKWKWMWNUOUWCUURUE
      ZUXBUWCUWPUXDUWCAGUURUWLUVPUWAUVEWOWPUURWQTZUXDUURUUSHZKUXBUXDCCWRUXFUURW
      SUUSUURUURUURAWTXAXBUUSUURXCVBTUVOUXCUUQUWBUVODDWRKZUXCUVOUVDUEUXGUVDWQUV
      DWSTUVDUVDXCVBXDUUSUVDUWQUWSXEXFUWCUWGUUSUWQAMZWIZUWRUWCUWGUURUWQWIZAMZUX
      IUWCEUWGUXKUWCUVQUWFHZUVQAHZLUVQUXJHZUXMLUVQUWGHUVQUXKHUWCUXMUXLUXNUVPUWB
      UXMUXLUXNXGUVPUWBUXMLZLZUXLUVQUWDHZUXNUXPUXMASIZUWDUEZUXLUXQXGUVPUWBUXMWJ
      UXPAGSUVOUUNUUPUXOVFVHVIUVPUWBUXSUXMUWCUXDUXSUXEUURXHWDXNUXMUXRUXSXIZUXLU
      XQUXTUXLUXQUXTUXQUXLUXTUWJUXQKZUVQUWEHZUXLKUXTUWEASUWIUXMUXRUXSXJVJUXTUYA
      UYBUXTUYALUXMUYAUYBUXMUXRUXSUYAXKUXTUYAXLUVQAUWDXMXOVTUWEUVQXPXQXRXSUXTUX
      QLZAUVQUBZVDZVEZUWFUVQUYCUWEUYEIZUYFUWFIUYCUYDUWDIZUYGUXTUXQUYHUXTUXSUXQU
      YHVCUXMUXRUXSXTZUVQUWDYETXSUYDUWDAYATUWEUYEYBTUYCUXRUVQSHZUVQUYFHUXMUXRUX
      SUXQYCUXTUXSUXQUYJUYIUWDUVQYDYOAUVQYFWGWPYGUPUWDUXJUVQUURYHYIYJYKYLUVQUWF
      AYMUVQUXJAYMYNYPUURUWQAYQYRUWAUXIUWRRUVPUVEUWAUXHUWQUUSUWAUWQAIUXHUWQRUUR
      AUUAUWQAUUBWDUUCUUDUUFUVGUWTRUWCUVDYHUOUUEUVSUWHEUWFAUVQUWFRUVRUWGUVGNUVQ
      UWFAYSYTUUGWGYKUUHUVSUVHECAECUDUVRUUSUVGNUVQUURAYSYTUUIUUJVTUUKUUL $.
      $( [1-Nov-2014] $)

    fin23lem23 $p |- ( ( ( S C_ om /\ -. S e. Fin ) /\ i e. om ) ->
      E! j e. S ( j i^i S ) ~~ i ) $=
      ( va com wss cfn wcel wa cv cin cen wbr wral wo wb sseldd con0 syl word
      wn wrex weq wi wreu fin23lem26 ensym entr sylan2 wceq simpl simprl onfin2
      vex inss2 eqsstri sseli inss1 ssfi sylancl simprr nnord ordtri2or2 syl2an
      syl2anc ssrin orim12i fin23lem25 ordom fin23lem24 mpanl1 bitrd ralrimivva
      syl3anc syl5ib ad2antrr ineq1 breq1d reu4 sylanbrc ) AEFZAGHUAZIBJZEHZICJ
      ZAKZWCLMZCAUBWGDJZAKZWCLMZIZCDUCZUDZDANCANZWGCAUEABCUFWAWNWBWDWAWMCDAAWKW
      FWILMZWAWEAHZWHAHZIZIZWLWJWGWCWILMWOWIWCBUNUGWFWCWIUHUIWSWOWFWIUJZWLWSWFG
      HZWIGHZWFWIFZWIWFFZOZWOWTPWSWEEHZXAWSAEWEWAWRUKZWAWPWQULQZXFWEGHWFWEFXAEG
      WEERGKGUMRGUOUPZUQWEAURWEWFUSUTSWSWHEHZXBWSAEWHXGWAWPWQVAQZXJWHGHWIWHFXBE
      GWHXIUQWHAURWHWIUSUTSWSWEWHFZWHWEFZOZXEWSXFXJXNXHXKXFWETWHTXNXJWEVBWHVBWE
      WHVCVDVEXLXCXMXDWEWHAVFWHWEAVFVGSWFWIVHVNETWAWRWTWLPVIEAWEWHVJVKVLVOVMVPW
      GWJCDAWLWFWIWCLWEWHAVQVRVSVT $.
      $( [1-Nov-2014] $)

    fin23lem22.b $e |- C = ( i e. om |-> U. { j e. S | ( j i^i S ) ~~ i } ) $.

    fin23lem22 $p |- ( ( S C_ om /\ -. S e. Fin ) -> C : om -1-1-onto-> S ) $=
      ( va com wss cfn wcel wa cv cin cen wbr ccrd cfv syl wceq wb wn crab cuni
      wreu fin23lem23 reucl simpll simpr sseldd con0 onfin2 inss2 eqsstri sseli
      inss1 ssfi mpan2 ficardom 3syl cardnn eqcomd eqeq1d eqcom syl6bb ad2antrl
      simprr sylancl ficarden syl2anc adantrr ineq1 breq1d reuuni2 3bitrd f1o2d
      weq ) BGHZBIJUAZKZCFGBDLZBMZCLZNOZDBUBUCZFLZBMZPQZAEVSWBGJZKWCDBUDZWDBJBC
      DUEZWCDBUFRVSWEBJZKZWEGJZWEIJZWGGJZWLBGWEVQVRWKUGVSWKUHUIGIWEGUJIMIUKUJIU
      LUMZUNZWNWFIJZWOWNWFWEHZWRWEBUOZWEWFUPZUQWFURRUSVSWHWKKZKZWBWGSZWGWBPQZSZ
      WFWBNOZWEWDSZWHXDXFTVSWKWHXDXEWGSXFWHWBXEWGWHXEWBWBUTVAVBXEWGVCVDVEXCWRWB
      IJZXFXGTXCWNWSWRXCWMWNXCBGWEVQVRXBUGVSWHWKVFZUIWQRWTXAVGWHXIVSWKGIWBWPUNV
      EWFWBVHVIXCXGWDWESZXHXCWKWIXGXKTXJVSWHWIWKWJVJWCXGDBWEDFVPWAWFWBNVTWEBVKV
      LVMVIWDWEVCVDVNVO $.
      $( [1-Nov-2014] $)
  $}


  ${
    $d U i u a b c d $.  $d A i u a b $.  $d i u t a b c d $.  $d B i u a b $.

    fin23lem.a $e |- U = seqom ( ( i e. om , u e. _V |-> if ( ( ( t ` i ) i^i
      u ) = (/) , u , ( ( t ` i ) i^i u ) ) ) , U. ran t ) $.

    $( The beginning of the proof proper that every II-finite set (every chain
       of subsets has a maximal element) is III-finite (has no denumerable
       collection of subsets).  The proof here is the only one I could find,
       from ~ http://matwbn.icm.edu.pl/ksiazki/fm/fm6/fm619.pdf p.94 (writeup
       by Tarski, credited to Kuratowski).  Translated into English and modern
       notation, the proof proceeds as follows (variables renamed for
       uniqueness):

       Suppose for a contradiction that ` A ` is a set which is II-finite but
       not III-finite.

       For any countable sequence of distinct subsets ` T ` of ` A ` , we can
       form a decreasing sequence of non-empty subsets ` ( U `` T ) ` by taking
       finite intersections of initial segments of ` T ` while skipping over
       any element of ` T ` which would cause the intersection to be empty.

       By II-finiteness (as ~ dffin2-4 ) this sequence contains its
       intersection, call it ` Y ` ; since by induction every subset in the
       sequence ` U ` is non-empty, the intersection must be non-empty.

       Suppose that an element ` X ` of ` T ` has non-empty intersection with
       ` Y ` .  Thus said element has a non-empty intersection with the
       corresponding element of ` U ` , therefore it was used in the
       construction of ` U ` and all further elements of ` U ` are subsets of
       ` X ` , thus ` X ` contains the ` Y ` .  That is, all elements of ` X `
       either contain ` Y ` or are disjoint from it.

       Since there are only two cases, there must exist an infinite subset of
       ` T ` which uniformly either contain ` Y ` or are disjoint from it.  In
       the former case we can create an infinite set by subtracting ` Y ` from
       each element.  In either case, call the result ` Z ` ; this is an
       infinite set of subsets of ` A ` , each of which is disjoint from ` Y `
       and contained in the union of ` T ` ; the union of ` Z ` is strictly
       contained in the union of ` T ` , because only the latter is a superset
       of the non-empty set ` Y ` .

       The preceeding four steps may be iterated a countable number of times
       starting from the assumed denumerable set of subsets to produce a
       denumerable sequence ` B ` of the ` T ` sets from each stage.  Great
       caution is required to avoid ~ ax-dc here; in particular an effective
       version of the pigeonhole principle (for aleph-null pigeons and 2 holes)
       is required.  Since a denumerable set of subsets is assumed to exist, we
       can conclude ` om e. _V ` without the axiom.

       This ` B ` sequence is strictly decreasing, thus it has no minimum,
       contradicting the first assumption.
    $)

    fin23lem12 $p |- ( A e. om -> ( U ` suc A ) = if ( ( ( t ` A ) i^i
        ( U ` A ) ) = (/) , ( U ` A ) , ( ( t ` A ) i^i ( U ` A ) ) ) ) $=
      ( com wcel csuc cfv cvv cv cin c0 wceq cif cmpt2 co eqeq1d ifbieq12d cuni
      seqomsuc fvex fveq2 ineq1d eqidd ineq2 eqid inex2 ifex ovmpt2 mpan2 eqtrd
      crn id1 ) CGHZCIDJCCDJZEAGKELZBLZJZALZMZNOZVAVBPZQZRZCUSJZUQMZNOZUQVHPZCV
      EDUSUNUAFUBUPUQKHVFVJOCDUCZEACUQGKVDVJVEVGVAMZNOZVAVLPURCOZVCVMVAVBVAVLVN
      VBVLNVNUTVGVAURCUSUDUEZSVNVAUFVOTVAUQOZVMVIVAVLUQVHVPVLVHNVAUQVGUGZSVPUOV
      QTVEUHVIUQVHVKUQVGVKUIUJUKULUM $.
      $( [1-Nov-2014] $)

    fin23lem13 $p |- ( A e. om -> ( U ` suc A ) C_ ( U ` A ) ) $=
      ( com wcel csuc cfv cv cin c0 wceq cif fin23lem12 wss ssid inss2 sseq1
      ifboth mp2an a1i eqsstrd ) CGHZCIDJCBKJZCDJZLZMNZUGUHOZUGABCDEFPUJUGQZUEU
      GUGQZUHUGQZUKUGRUFUGSUIULUMUKUGUHUGUJUGTUHUJUGTUAUBUCUD $.
      $( [1-Nov-2014] $)

    fin23lem14 $p |- ( ( A e. om /\ U. ran t =/= (/) ) ->
        ( U ` A ) =/= (/) ) $=
      ( va vb com cv c0 wne cfv wi wceq fveq2 neeq1d imbi2d eqnetrd adantr wcel
      crn cuni csuc weq cvv vex rnex uniex cin cif cmpt2 seqom0g a1i fin23lem12
      ax-mp wa iftrue simprr wn iffalse df-ne biimpri pm2.61ian ex imim2d finds
      id1 imp ) CIUABJZUBZUCZKLZCDMZKLZVMGJZDMZKLZNVMKDMZKLZNVMHJZDMZKLZNVMWAUD
      ZDMZKLZNVMVONGHCVPKOZVRVTVMWGVQVSKVPKDPQRGHUEZVRWCVMWHVQWBKVPWADPQRVPWDOZ
      VRWFVMWIVQWEKVPWDDPQRVPCOZVRVOVMWJVQVNKVPCDPQRVMVSVLKVSVLOZVMVLUFUAWKVKVJ
      BUGUHUIEAIUFEJVJMAJZUJZKOWLWMUKULDVLFUMUPUNVMVHSWAIUAZWCWFVMWNWCWFWNWCUQZ
      WEWAVJMWBUJZKOZWBWPUKZKWNWEWROWCABWADEFUOTWQWOWRKLWQWOUQWRWBKWQWRWBOWOWQW
      BWPURTWQWNWCUSSWQUTZWOUQWRWPKWSWRWPOWOWQWBWPVATWSWPKLZWOWTWSWPKVBVCTSVDSV
      EVFVGVI $.
      $( [1-Nov-2014] $)

    fin23lem15 $p |- ( ( ( A e. om /\ B e. om ) /\ B C_ A ) ->
        ( U ` A ) C_ ( U ` B ) ) $=
      ( vb va cv cfv wss csuc wceq fveq2 sseq1d weq com wcel wa ssid fin23lem13
      a1i wi ad2antrr sstr ex syl findsg ) HJZEKZDEKZLULULLZIJZEKZULLZUNMZEKZUL
      LZCEKZULLHICDUJDNUKULULUJDEOPHIQUKUOULUJUNEOPUJUQNUKURULUJUQEOPUJCNUKUTUL
      UJCEOPUMDRSZULUAUCUNRSZVATDUNLZTURUOLZUPUSUDVBVDVAVCABUNEFGUBUEVDUPUSURUO
      ULUFUGUHUI $.
      $( [1-Nov-2014] $)

    fin23lem16 $p |- U. ran U = U. ran t $=
      ( va vb crn cuni cv wss wcel cfv wceq com cvv c0 ax-mp peano1 mpan2 cmpt2
      unissb wrex wfn wb cin cif fnseqom fvelrnb wa 0ss fin23lem15 rnex seqom0g
      vex uniex syl6sseq sseq1 syl5ibcom rexlimiv sylbi fnfvelrn mp2an eqeltrri
      mprgbir elssuni eqssi ) CHZIZBJZHZIZVIVLKFJZVLKZFVHFVHVLUBVMVHLZGJZCMZVMN
      ZGOUCZVNCOUDZVOVSUEDAOPDJVJMAJZUFZQNWAWBUGUAZCVLEUHZGOVMCUIRVRVNGOVPOLZVQ
      VLKVRVNWEVQQCMZVLWEQOLZVQWFKZSWEWGUJQVPKWHVPUKABVPQCDEULTTVLPLWFVLNVKVJBU
      OUMUPWCCVLEUNRZUQVQVMVLURUSUTVAVEVLVHLVLVIKWFVLVHWIVTWGWFVHLWDSOQCVBVCVDV
      LVHVFRVG $.
      $( [1-Nov-2014] $)

    fin23lem17 $p |- ( U. ran t e. Fin2 -> |^| ran U e. ran U ) $=
      ( vb vc vd va cv wcel c0 wne wss wo wral wa wi wceq com crn cuni cint cpw
      cfin2 vex rnex uniex pweq pweqd raleqdv dffin2-4 elab2 fin23lem16 eqimssi
      sspwuni mpbir pwex elpw2 cdm wfn cvv cfv cin cif cmpt2 fnseqom fndm ax-mp
      peano1 ne0i eqnetri dm0rn0 necon3bii mpbi wrex wb fvelrnb word ordtri2or2
      nnord syl2anr fin23lem15 ancoms orim12d mpd sseq2 sseq1 orbi12d syl5ibcom
      ex rexlimdva imbi2d rexlimiv syl2anb rgen2a pm3.2i neeq1 raleq raleqbi1dv
      imp anbi12d inteq id eleq12d imbi12d rcla4v 3imp mp3an13 sylbi ) BJZUAZUB
      ZUEKFJZLMZGJZHJZNZXQXPNZOZHXNPZGXNPZQZXNUCZXNKZRZFXMUDZUDZPZCUAZUCZYJKZYF
      FIJZUDZUDZPYIIXMUEXLXKBUFUGUHZYMXMSZYFFYOYHYQYNYGYMXMUIUJUKIFGHULUMYJYHKZ
      YIYJLMZXTHYJPZGYJPZQZYLYRYJYGNZUUCYJUBZXMNUUDXMABCDEUNUOYJXMUPUQYJYGXMYPU
      RUSUQYSUUACUTZLMYSUUETLCTVAZUUETSDATVBDJXKVCAJZVDZLSUUGUUHVEVFCXMEVGZTCVH
      VILTKTLMVJTLVKVIVLUUELYJLCVMVNVOXTGHYJXPYJKZYMCVCZXPSZITVPZXNCVCZXQSZFTVP
      ZXTXQYJKZUUFUUJUUMVQUUIITXPCVRVIUUFUUQUUPVQUUIFTXQCVRVIUUMUUPXTUULUUPXTRZ
      ITYMTKZUUPUUKXQNZXQUUKNZOZRUULUURUUSUUOUVBFTUUSXNTKZQZUUKUUNNZUUNUUKNZOZU
      UOUVBUVDXNYMNZYMXNNZOZUVGUVCXNVSYMVSUVJUUSXNWAYMWAXNYMVTWBUVDUVHUVEUVIUVF
      UVDUVHUVEABYMXNCDEWCWKUVCUUSUVIUVFRUVCUUSQUVIUVFABXNYMCDEWCWKWDWEWFUUOUVE
      UUTUVFUVAUUNXQUUKWGUUNXQUUKWHWIWJWLUULUVBXTUUPUULUUTXRUVAXSUUKXPXQWHUUKXP
      XQWGWIWMWJWNXAWOWPWQYRYIUUBYLYFUUBYLRFYJYHXNYJSZYCUUBYEYLUVKXOYSYBUUAXNYJ
      LWRYAYTGXNYJXTHXNYJWSWTXBUVKYDYKXNYJXNYJXCUVKXDXEXFXGXHXIXJ $.
      $( [1-Nov-2014] $)

    fin23lem18 $p |- |^| ran U e. _V $=
      ( crn c0 wne cint cvv wcel cdm com wfn wceq cv cfv cin ax-mp mpbi fnseqom
      cif cmpt2 cuni fndm peano1 ne0i eqnetri dm0rn0 necon3bii intex ) CFZGHZUL
      IJKCLZGHUMUNMGCMNUNMODAMJDPBPZQAPZRZGOUPUQUBUCCUOFUDEUAMCUESGMKMGHUFMGUGS
      UHUNGULGCUIUJTULUKT $.
      $( [1-Nov-2014] $)

    fin23lem19 $p |- ( A e. om -> ( ( U ` suc A ) C_ ( t ` A ) \/
      ( ( U ` suc A ) i^i ( t ` A ) ) = (/) ) ) $=
      ( com wcel csuc cfv cv cin c0 wceq wss cif wa wn wo fin23lem12 eqif incom
      biimpi ineq2 eqeq1d biimprd impcom syl5eq inss1 sseq1 mpbiri orim12i 3syl
      adantl orcomd ) CGHZCIDJZCBKJZLZMNZUQUROZUPUQURCDJZLZMNZVBVCPNZVDUQVBNZQZ
      VDRZUQVCNZQZSZUTVASABCDEFTVEVKVDUQVBVCUAUCVGUTVJVAVGUSURUQLZMUQURUBVFVDVL
      MNZVFVMVDVFVLVCMUQVBURUDUEUFUGUHVIVAVHVIVAVCUROURVBUIUQVCURUJUKUNULUMUO
      $.
      $( [1-Nov-2014] $)

    fin23lem20 $p |- ( A e. om -> ( |^| ran U C_ ( t ` A ) \/ ( |^| ran U i^i
        ( t ` A ) ) = (/) ) ) $=
      ( com wcel crn cint csuc cfv wss cv cin c0 wceq wo wfn cvv cif cmpt2 cuni
      fnseqom peano2 fnfvelrn sylancr intss1 fin23lem19 sstr2 ssdisj ex orim12d
      syl sylc ) CGHZDIZJZCKZDLZMZUTCBNZLZMZUTVCOPQZRURVCMZURVCOPQZRUPUTUQHZVAU
      PDGSUSGHVHEAGTENVBLANZOZPQVIVJUAUBDVBIUCFUDCUEGUSDUFUGUTUQUHUNABCDEFUIVAV
      DVFVEVGURUTVCUJVAVEVGURUTVCUKULUMUO $.
      $( [1-Nov-2014] $)

    fin23lem21 $p |- ( ( U. ran t e. Fin2 /\ t : om -1-1-> _V ) ->
      |^| ran U =/= (/) ) $=
      ( va cv crn wcel com cvv c0 wne cfv wceq ax-mp wa cen wbr csdm cuni cfin2
      cint wf1 fin23lem17 wrex wfn wb cin cif fnseqom fvelrnb id1 csn cdif wf1o
      cmpt2 vex f1f1orn f1oen2g sylancr cdom wn cfn isfinite1 wi relen brrelexi
      snfi ensymg syl con3d anim2d mpi brsdom rnex sdomentr mpancom sdomdif wex
      sylibr n0 eldifsn wss elssuni ssn0 sylan sylbi exlimiv fin23lem14 syl2anr
      3syl neeq1 syl5ibcom rexlimdva syl5bi mpan9 ) BGZHZUAZUBICHZUCZXAIZJKWRUD
      ZXBLMZABCDEUEXCFGZCNZXBOZFJUFZXDXECJUGXCXIUHDAJKDGWRNAGZUIZLOXJXKUJUQCWTE
      UKFJXBCULPXDXHXEFJXDXFJIZQXGLMZXHXEXLXLWTLMZXMXDXLUMXDJWSRSZWSLUNZUOZLMZX
      NXDWRKIJWSWRUPXOBURZJKWRUSJWSKWRUTVAXOXPWSTSZXRXPJTSZXOXTXOXPJVBSZXPJRSZV
      CZQZYAXOYBJXPRSZVCZQZYEXPVDIYHLVIXPVEPXOYGYDYBXOYCYFXOJKIYCYFVFJWSRVGVHXP
      JKVJVKVLVMVNXPJVOWAWSKIYAXOQXTVFWRXSVPXPJWSKVQPVRXPWSVSVKXRXFXQIZFVTXNFXQ
      WBYIXNFYIXFWSIZXFLMZQXNXFWSLWCYJXFWTWDYKXNXFWSWEXFWTWFWGWHWIWHWLABXFCDEWJ
      WKXGXBLWMWNWOWPWQ $.
      $( [1-Nov-2014] $)
  $}

  ${
    $d x y z a b c d $.
    fin11a $p |- Fin C_ Fin1a $=
      ( va vb vc cfn cfin1a cv wcel cun wceq cin c0 wa wn wex unfir con3i eleq1
      simpld notbid syl5ibr imp ad2ant2r exlimivv con2i df-fin1a abeq2i sylibr
      ssriv ) ADEAFZDGZUIBFZCFZHZIZUKULJKIZLUKDGZMZULDGZMZLLZCNBNZMZUIEGVAUJUTU
      JMZBCUNUQVCUOUSUNUQVCUQVCUNUMDGZMVDUPVDUPURUKULORPUNUJVDUIUMDQSTUAUBUCUDV
      BAEABCUEUFUGUH $.
      $( [30-Oct-2014] $)

    fin1a2 $p |- Fin1a C_ Fin2 $=
      ? $.

    dffin4-2 $p |- Fin4 = { x | -. om ~<_ x } $=
      ( va vb cfin4 com cv cdom wbr wn cab wpss cen wa wex wcel infpssr exlimiv
      vex infpssALT impbii notbii df-fin4 abeq2i weq breq2 notbid 3bitr4i eqriv
      elab ) BDEAFZGHZIZAJZCFZBFZKUNUOLHMZCNZIZEUOGHZIZUODOUOUMOUQUSUQUSUPUSCUO
      UNBRZPQCUOVASTUAURBDBCUBUCULUTAUOVAABUDUKUSUJUOEGUEUFUIUGUH $.
      $( [30-Oct-2014] $)

    fin23 $p |- Fin2 C_ Fin3 $=
      ? $.

    fin34 $p |- Fin3 C_ Fin4 $=
      ( va vb cfin3 cfin4 cv cpw wcel com cdom wbr vex pwex wceq breq2 dffin4-2
      wn notbid elab2 csdm abeq2i domsdomtr mpan2 sdomdom con3i df-fin3 3imtr4i
      canth2 syl sylbi ssriv ) ACDAEZFZDGZHUKIJZPZUKCGUKDGUMHULIJZPZUOHBEZIJZPU
      QBULDUKAKZLURULMUSUPURULHINQBORUNUPUNHULSJZUPUNUKULSJVAUKUTUGHUKULUAUBHUL
      UCUHUDUIUMACAUETUOADAOTUFUJ $.
      $( [30-Oct-2014] $)

    dffin5-2 $p |- Fin5 = { x | -. ( x =/= (/) /\ x ~~ ( x +c x ) ) } $=
      ( va cfin5 cv c0 wne ccda co cen wbr wa wn cab csdm wo wcel wceq en0 biid
      necon2bbii bitri cdom brsdom cdadom3 mpbiran orbi12i ianor bitr4i df-fin5
      vex abeq2i weq neeq1 id oveq12 anidms breq12d anbi12d notbid elab 3bitr4i
      eqriv ) BCADZEFZVCVCVCGHZIJZKZLZAMZBDZEIJZVJVJVJGHZNJZOZVJEFZVJVLIJZKZLZV
      JCPVJVIPVNVOLZVPLZOVRVKVSVMVTVKVJEQVSVJRVOVJEVOSTUAVMVJVLUBJVTVJVLUCVJVJB
      UJZWAUDUEUFVOVPUGUHVNBCBUIUKVHVRAVJWAABULZVGVQWBVDVOVFVPVCVJEUMWBVCVJVEVL
      IWBUNWBVEVLQVCVJVCVJGUOUPUQURUSUTVAVB $.
      $( [30-Oct-2014] $)

    fin45 $p |- Fin4 C_ Fin5 $=
      ( va vb vc cfin4 cfin5 cv wpss cen wbr wa wex wn wne ccda c1o cxp c2o wss
      wcel ax-mp c0 co csuc sssucid df-2o sseqtr4i xpss2 a1i wel cop 1onn elexi
      n0 com sucid eleqtrri jctr opelxp sylibr nnord ordirr intnan mtbir nelne1
      word sylancl exlimiv sylbi necomd df-pss sylanbrc vex psseq2i sylib xp1en
      xp2cda entr mpan xpex wceq psseq1 breq1 anbi12d cla4ev syl2an wi cvv ovex
      ensym infpssen1 adantl mpd con3i df-fin4 abeq2i dffin5-2 3imtr4i ssriv )
      ADEBFZAFZGWSWTHIJBKZLZWTUAMZWTWTWTNUBZHIZJZLZWTDSWTESXFXAXFCFZXDGZXHXDHIZ
      JZCKZXAXCWTOPZXDGZXMXDHIZXLXEXCXMWTQPZGZXNXCXMXPRZXMXPMXQXRXCOQRXROOUCZQO
      UDUEUFOQWTUGTUHXCXPXMXCBAUIZBKXPXMMZBWTUMXTYABXTWSOUJZXPSZYBXMSZLYAXTXTOQ
      SZJYCXTYEOXSQOOUNUKULZUOUEUPUQWSOWTQYFURUSYDXTOOSZJYGXTOVEZYGLOUNSYHUKOUT
      TOVATVBWSOWTOYFURVCYBXPXMVDVFVGVHVIXMXPVJVKXPXDXMWTAVLZVPVMVNXMWTHIXEXOWT
      YIVOXMWTXDVQVRXKXNXOJCXMWTOYIYFVSXHXMVTXIXNXJXOXHXMXDWAXHXMXDHWBWCWDWEXEX
      LXAWFZXCXEXDWTHIWTWGSYJWTXDWTWTNWHWIYICBXDWTWJVFWKWLWMXBADABWNWOXGAEAWPWO
      WQWR $.
      $( [30-Oct-2014] $)

    fin56 $p |- Fin5 C_ Fin6 $=
      ( va cfin5 cfin6 cv cen wbr csdm wo cxp wcel wn cdom wi c2o cfn com ax-mp
      con0 cvv abeq2i c0 ccda co c1o w3o 3mix1 vex xp2cda wb cin onfin2 eqsstri
      inss2 2onn sselii fidomtri sdom2en01 xchbinx xpdom2 sylbir syl5eqbrr xpex
      wa sdomdomtr expcom com12 orrd df-3or sylibr jaoi df-fin5 df-fin6 3imtr4i
      syl ssriv ) ABCADZUAEFZVPVPVPUBUCZGFZHZVQVPUDEFZVPVPVPIZGFZUEZVPBJVPCJVQW
      DVSVQWAWCUFVSVQWAHZWCHWDVSWEWCWEKZVSWCWFVRWBLFZVSWCMWFVRVPNIZWBLVPAUGZUHW
      FNVPLFZWHWBLFWJVPNGFZWENOJWJWKKUIPONPROUJOUKROUMULUNUONVPUPQVPWIUQURNVPVP
      WIWIUSUTVAVSWGWCWBSJVSWGVCWCMVPVPWIWIVBVPVRWBSVDQVEVNVFVGVQWAWCVHVIVJVTAB
      AVKTWDACAVLTVMVO $.
      $( [29-Oct-2014] $)

    fin67 $p |- Fin6 C_ Fin7 $=
      ( va vb cfin6 cfin7 cv c0 cen wbr c1o csdm con0 com wn wcel cfn notbid wb
      cvv enfi mpan cxp w3o cdif wrex wa eldif onfin biimpar vex syl5ibrcom imp
      sylbi 0fin mpbiri nsyl 1onn nnsdom isfinite2 sdomirr eldifi omelon ontri1
      mp2b wss infxpen syl2anc sdomen2 sylancr mtbiri sdomen1 xpex anidms bitrd
      3ioran syl3anbrc rexlimiva con2i df-fin6 abeq2i df-fin7 3imtr4i ssriv
      xpen ) ACDAEZFGHZWDIGHZWDWDWDUAZJHZUBZWDBEZGHZBKLUCZUDZMZWDCNWDDNWMWIWKWI
      MZBWLWJWLNZWKUEZWEMWFMWHMZWOWQWDONZWEWPWKWSMZWPWTWKWJONZMZWPWJKNZWJLNZMZU
      EZXBWJKLUFZXCXBXEXCXAXDWJUGPUHULWKWSXAWJRNZWKWSXAQBUIZWDWJRSTPUJUKZWEWSFO
      NZUMXKWEWSXKQUMWDFOSTUNUOWQWSWFXJWFWSIONZILNILJHXLUPIUQIURVCZXLWFWSXLQXMW
      DIOSTUNUOWPWKWRWPWRWKWJWJWJUAZJHZMWPXOWJWJJHZWJUSWPXHXNWJGHZXOXPQXIWPXCLW
      JVDZXQWJKLUTWPXFXRXGXCXRXELKNXCXRXEQVALWJVBTUHULWJVEVFXNWJWJRVGVHVIWKWHXO
      WKWHWJWGJHZXOXHWKWHXSQXIWDWJWGRVJTWKXNRNWGXNGHZXSXOQWJWJXIXIVKWKXTWDWJWDW
      JXIXIWCVLWGXNWJRVGVHVMPUJUKWEWFWHVNVOVPVQWIACAVRVSWNADABVTVSWAWB $.
      $( [29-Oct-2014] $)

    fin71ac $p |- Fin7 C_ Fin $=
      ( va vb cfin7 cfn cv cen wbr con0 com cdif wrex wn wcel numth2 vex reximi
      wo ensym cun wceq wb uncom wss omsson undif mpbi eqtri rexeq ax-mp bitr3i
      rexun biimpi mp2b ori df-fin7 abeq2i isfi 3imtr4i ssriv ) ACDAEZBEZFGZBHI
      JZKZLZVBBIKZUTCMUTDMVDVFVAUTFGZBHKVBBHKZVDVFQZBUTNVGVBBHVAUTAORPVHVIVHVBB
      VCISZKZVIVJHTVKVHUAVJIVCSZHVCIUBIHUCVLHTUDIHUEUFUGVBBVJHUHUIVBBVCIUKUJULU
      MUNVEACABUOUPBUTUQURUS $.
      $( [29-Oct-2014] $)
  $}
