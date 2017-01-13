package il.ac.bgu.cs.fvm.impl;

import java.io.InputStream;
import java.util.*;

import il.ac.bgu.cs.fvm.channelsystem.ChannelSystem;
import il.ac.bgu.cs.fvm.channelsystem.InterleavingActDef;
import il.ac.bgu.cs.fvm.channelsystem.ParserBasedInterleavingActDef;
import il.ac.bgu.cs.fvm.nanopromela.NanoPromelaFileReader;
import il.ac.bgu.cs.fvm.nanopromela.NanoPromelaParser;
import il.ac.bgu.cs.fvm.nanopromela.NanoPromelaParser.StmtContext;
import il.ac.bgu.cs.fvm.programgraph.ActionDef;
import il.ac.bgu.cs.fvm.programgraph.ConditionDef;
import il.ac.bgu.cs.fvm.programgraph.PGTransition;
import il.ac.bgu.cs.fvm.programgraph.ParserBasedActDef;
import il.ac.bgu.cs.fvm.programgraph.ParserBasedCondDef;
import il.ac.bgu.cs.fvm.programgraph.ProgramGraph;
import il.ac.bgu.cs.fvm.transitionsystem.Transition;
import il.ac.bgu.cs.fvm.transitionsystem.TransitionSystem;
import il.ac.bgu.cs.fvm.util.Pair;
import static il.ac.bgu.cs.fvm.programgraph.ConditionDef.evaluate;

 
 public class FvmFacadeHelper
 {
	static FvmFacadeHelper instance;
	
	private FvmFacadeHelper(){
	}
	public static FvmFacadeHelper getInstance() {
		if(instance == null)
			instance = new FvmFacadeHelper();
		return instance;
	}
	
 /******************************
 	**** Private methods ****
 ******************************/

	private <L, A> ProgramGraph<L, A> createProgramGraph() {
		return new ProgramGraphImpl<L, A>();
	}
	
	private ProgramGraph<String, String> generatePGfromContext(StmtContext sc) {
		String terminate = "";
		ProgramGraph<String,String> pg = createProgramGraph();
        pg.addLocation(terminate);
        String root = sc.getText();
        pg.addLocation(root);
        pg.addInitialLocation(root);
        Map<String, Set<String>> subLocs = new HashMap<>();
        generatePGfromContext(sc, terminate, subLocs, pg);
        removeUnreachableStates(pg);
        return pg;
	}
	
 private <L, A> void removeUnreachableStates(ProgramGraph<L, A> pg) {
	 Set<L> reachLocs = reach(pg);
     Set<L> unReachLocs = pg.getLocations();
     unReachLocs.removeAll(reachLocs);
     Set<PGTransition<L, A>> PGtrpg = pg.getTransitions();
     for (L loc : unReachLocs) {
         for (PGTransition t : PGtrpg) {
             if (t.getFrom().equals(loc) || t.getTo().equals(loc)) {
                 pg.removeTransition(t);
             }
         }
         pg.removeLocation(loc);
     }		
}
 
 private <L, A> Set<L> reach(ProgramGraph<L, A> pg) {
	Set<L> reach = new HashSet<L>();
    Set<L> initStates = pg.getInitialLocations();
    for (L l : initStates) {
        Set<L> reached = new HashSet<L>();
        reachHelper(pg, l, reached);
        reach.addAll(reached);
    }
    return reach;
 }


private <L, A>  void reachHelper(ProgramGraph<L, A> pg, L l, Set<L> reached) {
	reached.add(l);
	Set<L> postStates = post(pg, l);
    for (L w : postStates) {
        if (!reached.contains(w)) {
        	reachHelper(pg, w, reached);
        }
    }
}

private <L, A> Set<L> post(ProgramGraph<L, A> pg, L l) {
	Set<L> post = new HashSet<L>();
    Set<PGTransition<L,A>> trans = pg.getTransitions();
    for (PGTransition t : trans) {
        if (t.getFrom().equals(l)) {
        	post.add((L)t.getTo());
        }
    }
    return post;
}
private <L, A> void generatePGfromContext(StmtContext sc, String terminate, Map<String, Set<String>> subLocs,
			ProgramGraph<String,String> pg) {

	String newL = sc.getText();
    pg.addLocation(newL);
    addSubItem(newL, newL, subLocs);
    if (sc.assstmt() != null || sc.chanreadstmt() != null || sc.chanwritestmt() != null ||
            sc.atomicstmt() != null || sc.skipstmt() != null) {
        PGTransition newTrpg = new PGTransition(newL, "", sc.getText(), terminate);
        pg.addTransition(newTrpg);
    }
    else if (sc.ifstmt() != null)
    {
        List<NanoPromelaParser.OptionContext> opts = sc.ifstmt().option();
        for (NanoPromelaParser.OptionContext optCon : opts){
            addSubItem(newL, optCon.stmt().getText(), subLocs);
            generatePGfromContext(optCon.stmt(), terminate, subLocs, pg);
            for (PGTransition tran :  pg.getTransitions())
            {
                if (tran.getFrom().equals((optCon.stmt().getText())))
                {
                    String cond = combineStmts(optCon.boolexpr().getText(), tran.getCondition());
                    PGTransition newTrpg = new PGTransition(newL, cond, tran.getAction(), tran.getTo());
                    pg.addTransition(newTrpg);
                }
            }
        }
    }
    else if (sc.dostmt() != null)
    {
        List<NanoPromelaParser.OptionContext> opts = sc.dostmt().option();
        StringBuilder sb = new StringBuilder();
        addSubItem(newL, terminate, subLocs);
        boolean start = true;
        for (NanoPromelaParser.OptionContext optCon : opts)
        {
            generatePGfromContext(optCon.stmt(), terminate, subLocs, pg);
            String newcurL = optCon.stmt().getText() + ";" + sc.getText();
            pg.addLocation(newcurL);
            addSubItem(newL, newcurL, subLocs);
            Set<String> helpSet = new HashSet<>();
            for (PGTransition<String, String> tran : pg.getTransitions())
            {
                if (tran.getFrom().equals(optCon.stmt().getText()))
                {
                    if (!tran.getTo().equals(terminate))
                    {
                        String curL = tran.getTo() + ";" + sc.getText();
                        pg.addLocation(curL);
                        addSubItem(newL, curL, subLocs);
                        helpSet.add(tran.getTo());
                        String cond = combineStmts(optCon.boolexpr().getText(), tran.getCondition());
                        PGTransition newTrpg = new PGTransition(newL, cond, tran.getAction(), curL);
                        pg.addTransition(newTrpg);
                    } else
                        {
                        String cond = combineStmts(optCon.boolexpr().getText(), tran.getCondition());
                        PGTransition newTrpg = new PGTransition(newL, cond, tran.getAction(), newL);
                        pg.addTransition(newTrpg);
                    }
                }
            }
            while (!helpSet.isEmpty()) {
                String loc = helpSet.iterator().next();
                helpSet.remove(loc);
                for (PGTransition<String, String> tran : pg.getTransitions()){
                    if (tran.getFrom().equals(loc)) {
                        if (!tran.getTo().equals(terminate)) {
                            String toLabel = tran.getTo();
                            String curL = toLabel + ";" + sc.getText();
                            if (!pg.getLocations().contains(curL))
                            {
                                pg.addLocation(curL);
                                addSubItem(newL, curL, subLocs);
                                helpSet.add(tran.getTo());
                            }
                            String locLabel = loc;
                            PGTransition<String, String> newTrpg = new PGTransition( locLabel + ";" + sc.getText(), tran.getCondition(), tran.getAction(), curL);
                            pg.addTransition(newTrpg);
                        } else
                            {
                            String locLabel = loc;
                            PGTransition<String, String> newTrpg = new PGTransition( locLabel + ";" + sc.getText(), tran.getCondition(), tran.getAction(), newL);
                            pg.addTransition(newTrpg);
                        }
                    }
                }
            }

            if (!"".equals(optCon.boolexpr().getText())){
                if (!start){
                    sb.append("||");
                }
                sb.append("("+optCon.boolexpr().getText()+")");
                start = false;
            }
        }
        PGTransition newTrpg = new PGTransition(newL, "!("+sb.toString()+")", "", terminate);
        pg.addTransition(newTrpg);
    } else {
        NanoPromelaParser.StmtContext stm1 = sc.stmt(0);
        NanoPromelaParser.StmtContext stm2 = sc.stmt(1);
        generatePGfromContext(stm1, terminate, subLocs, pg);
        generatePGfromContext(stm2, terminate, subLocs, pg);
        String s1Loc = stm1.getText();
        String s2Loc = stm2.getText();
        addSubItem(newL, s1Loc, subLocs);
        addSubItem(newL, s2Loc, subLocs);
        Set<String> helpSet = new HashSet<>();
        for (String l : getSubItems(s1Loc, subLocs)) {
            if (!l.equals(terminate)) {
                String addL = l + ";" + stm2.getText();
                pg.addLocation(addL);
                addSubItem(newL, addL, subLocs);
                helpSet.add(l);
            }
        }
        for (PGTransition<String, String> tran : pg.getTransitions()){
            if (helpSet.contains(tran.getFrom())) {
                String fromL = tran.getFrom() + ";" + stm2.getText();
                if (!tran.getTo().equals(terminate)){
                    String curL = tran.getTo() + ";" + stm2.getText();
                    pg.addLocation(curL);
                    pg.addLocation(fromL);
                    addSubItem(newL, curL, subLocs);
                    addSubItem(newL, fromL, subLocs);
                    PGTransition newTrpg = new PGTransition(fromL, tran.getCondition(), tran.getAction(), curL);
                    pg.addTransition(newTrpg);
                } else {
                    PGTransition newTrpg = new PGTransition(fromL, tran.getCondition(), tran.getAction(),stm2.getText());
                    pg.addTransition(newTrpg);
                }
            }
        }
    }		
}


private <L, A> List<L> generateStatesList(List<L> locList, int i, L toLoc)
{
    List<L> newLocList= new LinkedList<L> (locList);
    newLocList.set(i,toLoc);
    return newLocList;
}

private <L, A> List<L> generateStatesList(List<L> locList, int i, L toLoc, int j, L toLoc2)
{
    List<L> newLocList= new LinkedList<L> (locList);
    newLocList.set(i,toLoc);
    newLocList.set(j,toLoc2);
    return newLocList;
}

private String combineStmts(String s1, String s2) {
    String ans = "";
    if (!"".equals(s1)){
        ans += "("+s1+")";
    }
    if (!"".equals(ans) && !"".equals(s2)){
        ans += " && ";
    }
    if (!"".equals(s2)){
        ans += "("+s2+")";
    }
    return ans;
}

private void addSubItem(String locKey, String locToAdd, Map<String, Set<String>> subLocs) {
	Set<String> subItems = getSubItem(locKey, subLocs);
	subItems.add(locToAdd);
}

private Set<String> getSubItem(String locKey, Map<String, Set<String>> subLocs) {
	Set<String> subItems = subLocs.get(locKey);
    if (subItems == null) {
    	subItems = new HashSet<>();
        subLocs.put(locKey, subItems);
    }
    return subItems;
}

private Set<String> getSubItems(String l, Map<String, Set<String>> subs) {
    Set<String> subItems = new HashSet<>();
    subItems.add(l);
    Set<String> temp = new HashSet<>();
    boolean cond = true;
    while (cond){
        for (String loc : subItems) {
            Set<String> local = subs.get(loc);
            if (local != null) {
                temp.addAll(local);
            }
        }
        if (!subItems.addAll(temp)) {
            cond = false;
        }
    }
    return subItems;
}

private <L, A> Set<List<L>> getInitialLocs(List<ProgramGraph<L, A>> programGraphs, int size) {
	if (programGraphs.size() == size){
        List<L> l = new LinkedList<L>();
        Set<List<L>> s = new HashSet<List<L>>();
        s.add(l);
        return s;
    }

    Set<List<L>> ans = new HashSet<List<L>>();
    Set<List<L>> locations = getInitialLocs(programGraphs,size+1);
    ProgramGraph<L, A> pg = programGraphs.get(size);
    Set<L> initialLocations = pg.getInitialLocations();

    for(L location: initialLocations){
        for(List<L> l: locations){
            if(!l.isEmpty())
            {

                List<L> temp= new LinkedList<L>(l);
                temp.add(0,location);
                ans.add(temp);
            }
            else
            {
                List<L> temp= new LinkedList<L>();
                temp.add(location);
                ans.add(temp);
            }
        }
    }
    return ans;
}



private Set<List<String>> initMerge(Set<List<String>> InitSet1, Set<List<String>> InitSet2) {
	Set<List<String>> InitAns = new HashSet<>();
    for (List<String> ls1 : InitSet1)
    {
        for (List<String> ls2 : InitSet2)
        {
            boolean merge = true;

            for (String s1 : ls1) {
                for (String s2 : ls2) {

                    String name1, name2;
                    String val1, val2;
                    if (s1.contains(":=")) {
                        name1 = s1.split(":=")[0];
                        val1 = s1.split(":=")[1];
                    } 
                    else {
                        name1 = s1;
                        val1 = s1;
                    }

                    if (s2.contains(":=")) {
                        name2 = s2.split(":=")[0];
                        val2 = s2.split(":=")[1];
                    } 
                    else {
                        name2 = s2;
                        val2 = s2;
                    }
                    if (name1.equals(name2) && !val1.equals(val2)) {
                        merge = false;
                        break;
                    }
                }
            }
            if (merge) {
                List<String> temp = new ArrayList<String>(ls1);
                temp.addAll(ls2);
                InitAns.add((new ArrayList<String>(new LinkedHashSet<String>(temp))));
            }
        }
    }
    return InitAns;
}


private <A, L> TransitionSystem<Pair<List<L>, Map<String, Object>>, A, String> TSfromCShelper(Set<InterleavingActDef> intrleaveDefs,Set<ConditionDef> condDefs,Set<ActionDef> actDefs ,
																								ChannelSystem<L, A> cs,TransitionSystem ans, int size){
	boolean cond = true;
    while (cond)
    {
        Set<Pair<List<L>,Map<String, Object>>> oldStates = ans.getStates();
        for(Pair<List<L>,Map<String, Object>> state : oldStates)
        {
            for(int i=0 ; i < size; i++)
            {
                ProgramGraph<L,A> pg = cs.getProgramGraphs().get(i);
                Set<PGTransition<L,A>> allTrans = pg.getTransitions();
                for(PGTransition<L,A> trans : allTrans)
                {
                    if(trans.getFrom().equals(state.getFirst().get(i)))
                    {
                        if (evaluate(condDefs, state.getSecond(), trans.getCondition()))
                        {
                            if (InterleavingActDef.isOneSidedAction(intrleaveDefs, (String) trans.getAction()))
                            {
                                for(int j=i+1 ; j < size ; j++ )
                                {
                                    ProgramGraph<L,A> pg2 = cs.getProgramGraphs().get(j);
                                    Set<PGTransition<L,A>> allTrans2 = pg2.getTransitions();

                                    for(PGTransition<L,A> trans2 : allTrans2)
                                    {
                                        if(trans2.getFrom().equals(state.getFirst().get(j)))
                                        {
                                            if(evaluate(condDefs, state.getSecond(), trans2.getCondition()))
                                            {
                                                if(InterleavingActDef.isOneSidedAction(intrleaveDefs, (String) trans2.getAction()))
                                                {
                                                    String newAction = trans.getAction() + "|" + trans2.getAction();

                                                    if (InterleavingActDef.isMatchingAction(intrleaveDefs, newAction))
                                                    {
                                                        List<L> newStateList = generateStatesList(state.getFirst(), i, trans.getTo(), j , trans2.getTo());

                                                        Map<String, Object> val = new LinkedHashMap<>();

                                                        val = ActionDef.effect(actDefs, state.getSecond(),"" );

                                                        if (val != null)
                                                        {
                                                            Pair<List<L>, Map<String, Object>> newState = new Pair(newStateList, val);
                                                            ans.addState(newState);
                                                            for (Map.Entry<String, Object> entry : val.entrySet())
                                                            {
                                                                String AP = entry.getKey() + " = " + entry.getValue();

                                                                ans.addAtomicProposition(AP);
                                                                ans.addToLabel(newState, AP);

                                                            }

                                                            ans.addAtomicProposition(trans.getTo());
                                                            ans.addToLabel(newState, trans.getTo());

                                                            ans.addAction(newAction);
                                                            Transition t = new Transition(state, newAction, newState);
                                                            ans.addTransition(t);
                                                        }
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                            else
                            {
                                List<L> newStateList = generateStatesList(state.getFirst(), i, trans.getTo());
                                Map<String, Object> val = new LinkedHashMap<>();

                                val = ActionDef.effect(actDefs, state.getSecond(), trans.getAction());

                                if (val != null)
                                {
                                    Pair<List<L>, Map<String, Object>> newState = new Pair(newStateList, val);
                                    ans.addState(newState);
                                    for (Map.Entry<String, Object> entry : val.entrySet())
                                    {
                                        String AP = entry.getKey() + " = " + entry.getValue();

                                        ans.addAtomicProposition(AP);
                                        ans.addToLabel(newState, AP);

                                    }

                                    ans.addAtomicProposition(trans.getTo());
                                    ans.addToLabel(newState, trans.getTo());

                                    ans.addAction(trans.getAction());
                                    Transition t = new Transition(state, trans.getAction(), newState);
                                    ans.addTransition(t);
                                }
                            }
                        }
                    }
                }
            }
        }

        if (ans.getStates().equals(oldStates))
        {
            cond = false;
        }
    }

    return ans;
}

private <L1, L2, A> ProgramGraph interleavePGsHelper(ProgramGraph<L1, A> pg1, ProgramGraph<L2, A> pg2,
															Map<L1, Map<L2,Pair<L1,L2>>> loc1loc2, Map<L2, Map<L1,Pair<L1,L2>>> loc2loc1) {
        ProgramGraph<L1,A> interleavePG = createProgramGraph();
        Set<List<String>> pg1init = pg1.getInitalizations();
        Set<List<String>> pg2init = pg2.getInitalizations();

        for (List<String> l1 : pg1init){
            for (List<String> l2 : pg2init){

                boolean shouldUnite = true;
                for (String s1 : l1){
                    for (String s2 : l2){

                        String name1, name2;
                        String val1, val2;
                        if (s1.contains(":="))
                        {
                            name1 = s1.split(":=")[0];
                            val1 = s1.split(":=")[1];
                        }
                        else
                        {
                            name1 = s1;
                            val1 = s1;
                        }

                        if (s2.contains(":=")){
                            name2 = s2.split(":=")[0];
                            val2 = s2.split(":=")[1];
                        }
                        else
                        {
                            name2 = s2;
                            val2 = s2;
                        }

                        if (name1.equals(name2) && !val1.equals(val2)){
                            shouldUnite = false;
                            break;
                        }
                    }
                }
                if (shouldUnite)
                {
                    List<String> temp = new ArrayList<String>(l1);
                    temp.addAll(l2);
                    interleavePG.addInitalization(new ArrayList<String>(new LinkedHashSet<String>(temp)));
                }
            }
        }


        Set<L1> initialLocs1 = pg1.getInitialLocations();
        Set<L2> initialLocs2 = pg2.getInitialLocations();

        for (Object l1 : pg1.getLocations()) {
            for (Object l2 : pg2.getLocations()) {

                Pair<L1,L2> newLoc = new Pair(l1,l2);
                interleavePG.addLocation((L1) newLoc);
                if (initialLocs1.contains(l1) && initialLocs2.contains(l2)) {
                	interleavePG.addInitialLocation((L1) newLoc);
                }
                Map<L2,Pair<L1,L2>> l2ToPair = loc1loc2.get(l1);
                if (l2ToPair == null) {
                    l2ToPair = new HashMap<>();
                    loc1loc2.put((L1)l1, l2ToPair);
                }

                Map<L1,Pair<L1,L2>> l1ToPair = loc2loc1.get(l2);
                if (l1ToPair == null) {
                    l1ToPair = new HashMap<>();
                    loc2loc1.put((L2)l2, l1ToPair);
                }

                l2ToPair.put((L2)l2, newLoc);
                l1ToPair.put((L1)l1, newLoc);
            }
        }

        return interleavePG;
}

/******************************
 	**** Public methods ****
 ******************************/
	
	public ProgramGraph<String, String> PGfromNanoPromela(String filename) throws Exception {
		NanoPromelaParser.StmtContext sc = NanoPromelaFileReader.pareseNanoPromelaFile(filename);
        return generatePGfromContext(sc);
	}
	

	public ProgramGraph<String, String> PGfromNanoPromelaString(String nanopromela) throws Exception {
		NanoPromelaParser.StmtContext sc = NanoPromelaFileReader.pareseNanoPromelaString(nanopromela);
        return generatePGfromContext(sc);
	}

	public ProgramGraph<String, String> PGfromNanoPromela(InputStream inputStream) throws Exception {
		Scanner s = new Scanner(inputStream).useDelimiter("\\A");
        return PGfromNanoPromelaString(s.hasNext() ? s.next() : "");
	}
	
	public <L, A, P, S> TransitionSystem<Pair<List<L>, Map<String, Object>>, A, String> TSfromChannelSystem(ChannelSystem<L, A> cs) {
		Set<ActionDef> actDefs = new HashSet<>();
        Set<ConditionDef> condDefs = new HashSet<>();
        Set<InterleavingActDef> intrleaveDefs = new HashSet<>();
        actDefs.add(new ParserBasedInterleavingActDef());
        actDefs.add(new ParserBasedActDef());
        intrleaveDefs.add(new ParserBasedInterleavingActDef());
        condDefs.add(new ParserBasedCondDef());
        TransitionSystem ans = new TransitionSystemImpl<S, A, P>();
        Set<List<L>> locations = getInitialLocs(cs.getProgramGraphs(), 0);

        int size = cs.getProgramGraphs().size();

        Set<List<String>> finalInitSet = new HashSet<>();
        List<String> lst = new LinkedList<>();
        finalInitSet.add(lst);

        for(int i = 0; i < size; i++)
        {
            if (!cs.getProgramGraphs().get(i).getInitalizations().isEmpty())
                finalInitSet = initMerge(finalInitSet, cs.getProgramGraphs().get(i).getInitalizations());
        }

        for(List<L> initLoc : locations )
        {
            if (finalInitSet.size()==1 && finalInitSet.contains(lst))
            {
                Map<String, Object> mapping = new HashMap<>();
                Pair<List<L>, Map<String, Object>> newState = new Pair(initLoc, mapping);
                ans.addState(newState);
                ans.addInitialState(newState);
            }
            else
            {
                for (List<String> initials : finalInitSet)
                {
                    Map<String, Object> val = new LinkedHashMap<>();
                    for (String init : initials)
                    {
                        val = ActionDef.effect(actDefs, val, init);
                    }

                    Pair<List<L>, Map<String, Object>> newState = new Pair(initLoc, val);
                    ans.addState(newState);
                    ans.addInitialState(newState);
                    for (Map.Entry<String, Object> entry : val.entrySet())
                    {
                        String AP = entry.getKey() + " = " + entry.getValue();
                        ans.addAtomicProposition(AP);
                        ans.addToLabel(newState,AP);
                    }

                    ans.addAtomicProposition(initLoc);
                    ans.addToLabel(newState,initLoc);
                }
            }
        }
        return TSfromCShelper(intrleaveDefs,condDefs,actDefs,cs, ans, size);
 }
	
	public <L1, L2, A> ProgramGraph<Pair<L1, L2>, A> interleavePGs(ProgramGraph<L1, A> pg1, ProgramGraph<L2, A> pg2) {
		Map<L1, Map<L2,Pair<L1,L2>>> loc1loc2 = new HashMap<>();
        Map<L2, Map<L1,Pair<L1,L2>>> loc2loc1 = new HashMap<>();
        ProgramGraph ans = interleavePGsHelper(pg1, pg2, loc1loc2, loc2loc1);
        Set<PGTransition<L1, A>> pg1trans = pg1.getTransitions();
        Set<PGTransition<L2, A>> pg2trans = pg2.getTransitions();

        for (PGTransition t : pg1trans) {
            Map<L2,Pair<L1,L2>> l2ToPairFrom = loc1loc2.get(t.getFrom());
            if (l2ToPairFrom == null) {
                l2ToPairFrom = new HashMap<>();
                loc1loc2.put( (L1) t.getFrom(), l2ToPairFrom);
            }
            Map<L2,Pair<L1,L2>> l2ToPairTo = loc1loc2.get(t.getTo());
            if (l2ToPairTo == null) {
                l2ToPairTo = new HashMap<>();
                loc1loc2.put( (L1) t.getTo(), l2ToPairTo);
            }
            for (L2 l2 : l2ToPairFrom.keySet()) {
                Pair<L1,L2> toLocOnl2 = l2ToPairTo.get(l2);
                PGTransition newT = new PGTransition(l2ToPairFrom.get(l2), t.getCondition(), t.getAction(), toLocOnl2);
                ans.addTransition(newT);
            }
        }

        for (PGTransition t : pg2trans) {
            Map<L1,Pair<L1,L2>> l1ToPairFrom = loc2loc1.get(t.getFrom());
            if (l1ToPairFrom == null) {
                l1ToPairFrom = new HashMap<>();
                loc2loc1.put( (L2) t.getFrom(), l1ToPairFrom);
            }

            Map<L1,Pair<L1,L2>> l1ToPairTo = loc2loc1.get(t.getTo());
            if (l1ToPairTo == null) {
                l1ToPairTo = new HashMap<>();
                loc2loc1.put( (L2) t.getTo(), l1ToPairTo);
            }
            for (L1 l1 : l1ToPairFrom.keySet()) {
                Pair<L1,L2> toLocOnl2 = l1ToPairTo.get(l1);
                PGTransition newT = new PGTransition(l1ToPairFrom.get(l1), t.getCondition(), t.getAction(), toLocOnl2);
                ans.addTransition(newT);
            }
        }
        removeUnreachableStates(ans);
        return ans;
	}
}