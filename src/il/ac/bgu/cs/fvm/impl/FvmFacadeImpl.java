package il.ac.bgu.cs.fvm.impl;

import il.ac.bgu.cs.fvm.FvmFacade;
import il.ac.bgu.cs.fvm.automata.Automaton;
import il.ac.bgu.cs.fvm.channelsystem.ChannelSystem;
import il.ac.bgu.cs.fvm.circuits.Circuit;
import il.ac.bgu.cs.fvm.exceptions.ActionNotFoundException;
import il.ac.bgu.cs.fvm.exceptions.StateNotFoundException;
import il.ac.bgu.cs.fvm.programgraph.ActionDef;
import il.ac.bgu.cs.fvm.programgraph.ConditionDef;
import il.ac.bgu.cs.fvm.programgraph.ProgramGraph;
import il.ac.bgu.cs.fvm.transitionsystem.AlternatingSequence;
import il.ac.bgu.cs.fvm.transitionsystem.Transition;
import il.ac.bgu.cs.fvm.transitionsystem.TransitionSystem;
import il.ac.bgu.cs.fvm.util.Pair;
import java.io.InputStream;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * Implement the methods in this class. You may add additional classes as you
 * want, as long as they live in the {@code impl} package, or one of its 
 * sub-packages.
 */
public class FvmFacadeImpl implements FvmFacade {

    @Override
    public <S, A, P> TransitionSystem<S, A, P> createTransitionSystem() {
        return new TransitionSystemImpl<S, A, P>();
    }

    @Override
    public <S, A, P> boolean isActionDeterministic(TransitionSystem<S, A, P> ts) {
        boolean isDet=true;
        Set<A> tsActions = ts.getActions();
        Set<S> tsStates = ts.getStates();
        isDet &= ts.getInitialStates().size()<2;
        for (A a : tsActions) {
        	for (S s : tsStates) {
        		if(isDet){
            		isDet &= post(ts,s, a).size() <2;
            	}
            	else break;
			}
		}
        return isDet;
    }

	@Override
    public <S, A, P> boolean isAPDeterministic(TransitionSystem<S, A, P> ts) {
		boolean isDet = true;
        isDet &= ts.getInitialStates().size()<2;
        Set<S> tsStates = ts.getStates();
        Set<S> postStates;
        for (S s : tsStates) {
        	if(isDet){
        		postStates = post(ts, s);
    			isDet &= isAPpostUnique(postStates,ts.getLabelingFunction());
        	}
        	else break;
		}
        return isDet;
    }

	@Override
    public <S, A, P> boolean isExecution(TransitionSystem<S, A, P> ts, AlternatingSequence<S, A> e) {
        return isInitialExecutionFragment(ts, e) && isMaximalExecutionFragment(ts, e);
    }

	
	@Override
	public <S, A, P> boolean isExecutionFragment(TransitionSystem<S, A, P> ts, AlternatingSequence<S, A> e) {
		if(!ts.getStates().contains(e.head()))
    		throw new StateNotFoundException(e.head());
		else if (e.size()==1) return true;
		else{
			AlternatingSequence<A, S> tail = e.tail();
			S from = e.head();
			A act = tail.head();
			S to = tail.tail().head();
			Set<S> postStates;
			if(ts.getActions().contains(act)){
				postStates = post(ts,from,act);
				return postStates.contains(to) && isExecutionFragment(ts,tail.tail());
			}
			else throw new ActionNotFoundException(act);
		}
	}

    @Override
    public <S, A, P> boolean isInitialExecutionFragment(TransitionSystem<S, A, P> ts, AlternatingSequence<S, A> e) {
        S firstState = e.head();
        return ts.getInitialStates().contains(firstState) && isExecutionFragment(ts, e);
    }

    @Override
    public <S, A, P> boolean isMaximalExecutionFragment(TransitionSystem<S, A, P> ts, AlternatingSequence<S, A> e) {
        S lastState = e.last();
        return isStateTerminal(ts, lastState) && isExecutionFragment(ts, e);
    }

    @Override
    public <S, A> boolean isStateTerminal(TransitionSystem<S, A, ?> ts, S s) {
        if(ts.getStates().contains(s))
        	return post(ts,s).isEmpty();
        else throw new StateNotFoundException(s);
    }

    @Override
    public <S> Set<S> post(TransitionSystem<S, ?, ?> ts, S s) {
    	Set<?> trans = ts.getTransitions();
        Set<S> postStates = new HashSet<S>(); 
    	for (Object t : trans) {
			if(((Transition)t).getFrom().equals(s))
				postStates.add((S) ((Transition)t).getTo());
		}
        return postStates;
    }

    @Override
    public <S> Set<S> post(TransitionSystem<S, ?, ?> ts, Set<S> c) {
        Set<S> postStates = new HashSet<S>();
        for (S cs : c) {
			postStates.addAll(post(ts,cs));
		}
        return postStates;
    }

    @Override
    public <S, A> Set<S> post(TransitionSystem<S, A, ?> ts, S s, A a) {
    	Set<Transition<S,A>> trans = ts.getTransitions();
        Set<S> postStates = new HashSet<S>();
        for (Transition t : trans) {
        	if(t.getFrom().equals(s) && t.getAction().equals(a))
        		postStates.add((S)t.getTo());
		}
        return postStates;
    }

    @Override
    public <S, A> Set<S> post(TransitionSystem<S, A, ?> ts, Set<S> c, A a) {
    	Set<S> postStates = new HashSet<S>();
	  	for (S cs : c) {
	  		postStates.addAll(post(ts,cs,a));
  		}
        return postStates;   
    }

    @Override
    public <S> Set<S> pre(TransitionSystem<S, ?, ?> ts, S s) {
    	Set<?> trans = ts.getTransitions();
        Set<S> preStates = new HashSet<S>();
        Transition t;
        for (Object o : trans) {
        	t = (Transition) o;
			if(t.getTo().equals(s))
				preStates.add((S) t.getFrom());
		}
        return preStates;
    }

    @Override
    public <S> Set<S> pre(TransitionSystem<S, ?, ?> ts, Set<S> c) {
    	Set<S> preStates = new HashSet<S>();
    	for (S cs : c) {
			preStates.addAll(pre(ts,cs));
		}
    	return preStates;
    }

    @Override
    public <S, A> Set<S> pre(TransitionSystem<S, A, ?> ts, Set<S> c, A a) {
    	Set<S> preStates = new HashSet<S>();
    	for (S cs : c) {
			preStates.addAll(pre(ts,cs,a));
		}
    	return preStates;
    }

    @Override
    public <S, A> Set<S> pre(TransitionSystem<S, A, ?> ts, S s, A a) {
    	Set<?> trans = ts.getTransitions();
        Set<S> preStates = new HashSet<S>();
        Transition t;
        for (Object o : trans) {
        	t = (Transition) o;
			if(t.getTo().equals(s) && t.getAction().equals(a))
				preStates.add((S) t.getFrom());
		}
        return preStates;
    }

    @Override
    public <S, A> Set<S> reach(TransitionSystem<S, A, ?> ts) {
    	Set<S> initStates = ts.getInitialStates();
    	Set<S> tsReach = new HashSet<S>();
    	Set<S> allPosts;
    	for (S is : initStates) {
    		allPosts= new HashSet<S>();
    		allPosts.add(is);
    		getAllPosts(ts, post(ts,is),allPosts);
    		tsReach.addAll(allPosts);
		}
    	return tsReach;
    }

	private <S,A,P> boolean isAPpostUnique(Set<S> postStates, Map<S, Set<P>> labelFunc) {
    	Set<P> tags;
    	Set<Set<P>> postStatesTags = new HashSet<Set<P>>();
    	for (S s : postStates) {
			tags = labelFunc.get(s);
			if(postStatesTags.contains(tags))
				return false;
			else postStatesTags.add(tags);
		}
		return true;
	}
	
	private <S, A> void getAllPosts(TransitionSystem<S, A, ?> ts,Set<S> post,Set<S> allPosts) {
		for (S as : post) {
			if(allPosts.contains(as))
				continue;
			else{
				allPosts.add(as);
				getAllPosts(ts, post(ts,as), allPosts);
			}
		}
	}
        
    /*******************************************************
     ************ 		HW1 Ends Here!         *************
     *******************************************************/

    @Override
    public <S1, S2, A, P> TransitionSystem<Pair<S1, S2>, A, P> interleave(TransitionSystem<S1, A, P> ts1, TransitionSystem<S2, A, P> ts2) {
        throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement interleave
    }

    @Override
    public <S1, S2, A, P> TransitionSystem<Pair<S1, S2>, A, P> interleave(TransitionSystem<S1, A, P> ts1, TransitionSystem<S2, A, P> ts2, Set<A> handShakingActions) {
        throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement interleave
    }

    @Override
    public <L, A> ProgramGraph<L, A> createProgramGraph() {
       return new ProgramGraphImpl<L, A>();
    }

    @Override
    public <L1, L2, A> ProgramGraph<Pair<L1, L2>, A> interleave(ProgramGraph<L1, A> pg1, ProgramGraph<L2, A> pg2) {
        throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement interleave
    }

    @Override
    public TransitionSystem<Pair<List<Boolean>, List<Boolean>>, List<Boolean>, Object> transitionSystemFromCircuit(Circuit c) {
    	TransitionSystem<Pair<List<Boolean>, List<Boolean>>, List<Boolean>, Object> ansTs = new TransitionSystemImpl<>();
    	List<String> inputs = c.getInputPortNames();
        List<String> registers = c.getRegisterNames();
        
        
    	throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement transitionSystemFromCircuit
    }
    
    private void genStates(List<String> in, List<String>reg, TransitionSystem<Pair<List<Boolean>, List<Boolean>>, List<Boolean>, Object> ts){
    	for (int i = 0; i < in.size(); i++){
    		for(int j = 0; j < reg.size();j++){
    			
    		}
    	}
    }

    @Override
    public <L, A> TransitionSystem<Pair<L, Map<String, Object>>, A, String> transitionSystemFromProgramGraph(ProgramGraph<L, A> pg, Set<ActionDef> actionDefs, Set<ConditionDef> conditionDefs) {
        throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement transitionSystemFromProgramGraph
    }

    @Override
    public <L, A> TransitionSystem<Pair<List<L>, Map<String, Object>>, A, String> transitionSystemFromChannelSystem(ChannelSystem<L, A> cs) {
        throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement transitionSystemFromChannelSystem
    }

    @Override
    public ProgramGraph<String, String> programGraphFromNanoPromela(String filename) throws Exception {
        throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement programGraphFromNanoPromela
    }

    @Override
    public ProgramGraph<String, String> programGraphFromNanoPromelaString(String nanopromela) throws Exception {
        throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement programGraphFromNanoPromelaString
    }

    @Override
    public ProgramGraph<String, String> programGraphFromNanoPromela(InputStream inputStream) throws Exception {
        throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement programGraphFromNanoPromela
    }

    /*******************************************************
     ************ 		HW2 Ends Here!         *************
     *******************************************************/

    @Override
    public <Sts, Saut, A, P> TransitionSystem<Pair<Sts, Saut>, A, P> product(TransitionSystem<Sts, A, P> ts, Automaton<Saut, P> aut) {
        throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement product
    }

    

}
