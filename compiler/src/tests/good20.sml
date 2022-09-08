fun celtics x = (print "Larry Bird\n";
                 print "Kevin McHale\n";
                 print "Robert Parish\n";
                 print "Dennis Johnson\n";
                 print "Danny Ainge\n");

fun lakers x =
    let val SF = "James Worthy\n"
        val PF = "A.C. Green\n"
        val C  = "Kareem Abdul-Jabaar\n"
        val PG = "Magic Johnson\n"
        val SG = "Byron Scott\n"
    in
        print SF;
        print PF;
        print C;
        print PG;
        print SG
    end;

val _ = "sequences of expressions"
