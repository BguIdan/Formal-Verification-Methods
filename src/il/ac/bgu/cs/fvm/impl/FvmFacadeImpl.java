package il.ac.bgu.cs.fvm.impl;

import il.ac.bgu.cs.fvm.FvmFacade;
import il.ac.bgu.cs.fvm.automata.Automaton;
import il.ac.bgu.cs.fvm.channelsystem.ChannelSystem;
import il.ac.bgu.cs.fvm.circuits.Circuit;
import il.ac.bgu.cs.fvm.examples.VendingMachineBuilder.ACTION;
import il.ac.bgu.cs.fvm.examples.VendingMachineBuilder.STATE;
import il.ac.bgu.cs.fvm.exceptions.ActionNotFoundException;
import il.ac.bgu.cs.fvm.exceptions.StateNotFoundException;
import il.ac.bgu.cs.fvm.programgraph.*;
import il.ac.bgu.cs.fvm.transitionsystem.AlternatingSequence;
import il.ac.bgu.cs.fvm.transitionsystem.Transition;
import il.ac.bgu.cs.fvm.transitionsystem.TransitionSystem;
import il.ac.bgu.cs.fvm.util.Pair;
import java.io.InputStream;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import static il.ac.bgu.cs.fvm.programgraph.ConditionDef.evaluate;


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
	private <S, A, P>  void removeUnreachableStates(TransitionSystem<S, A, P> ts) {

		Set<S> reachableStates = reach(ts);
		Set<S> allStates = ts.getStates();
		Set<S> unreachables = new HashSet<>();
		for(S s : allStates){
			unreachables.add(s);
		}
		for(S s : reachableStates){
			unreachables.remove(s);
		}
		Set<S> initialStates = ts.getInitialStates();
		Map<S, Set<P>> labeling = ts.getLabelingFunction();
		Set<Transition<S,A>> transitions = ts.getTransitions();
		for (S s : unreachables) {
			if (initialStates.contains(s)) {
				ts.removeInitialState(s);
			}
			Set<P> labelsOfState = labeling.get(s);
			if (labelsOfState != null && labelsOfState.size() > 0) {
				for (P l : labelsOfState) {
					ts.removeLabel(s, l);
				}
			}
			for (Transition t : transitions) {
				if (t.getFrom().equals(s) || t.getTo().equals(s)) {
					ts.removeTransition(t);
				}
			}
			ts.removeState(s);
		}
	}

	private <S1, S2, A, P> void addLabelingToStates(Set<P> lablesMap,Pair<S1, S2> interState, TransitionSystem<Pair<S1, S2>, A, P> ts){
		for(P p : lablesMap){
			ts.addToLabel(interState, p);
		}
	}

	private <S1, S2, A, P> void createStatesWithLabeling(TransitionSystem<S1, A, P> ts1, TransitionSystem<S2, A, P> ts2, 
			Map<S1, Map<S2,Pair<S1,S2>>> dynamicMapStatesS1Leads, Map<S2, Map<S1,Pair<S1,S2>>> dynamicMapStatesS2Leads, TransitionSystem<Pair<S1, S2>, A, P> ts){
		Set<S1> initialsS1 = ts1.getInitialStates();
		Set<S2> initialsS2 = ts2.getInitialStates();
		Map<S1, Set<P>> labelingS1 = ts1.getLabelingFunction();
		Map<S2, Set<P>> labelingS2 = ts2.getLabelingFunction();
		Set<S1> statesS1 = ts1.getStates();
		Set<S2> statesS2 = ts2.getStates();
		for(S1 state1 : statesS1){
			for(S2 state2 : statesS2){
				Pair<S1, S2> interState = new Pair<S1, S2>(state1, state2);
				ts.addState(interState);
				// if both initial states in their ts's
				if(initialsS1.contains(state1) && initialsS2.contains(state2)){
					ts.addInitialState(interState);
				}
				addLabelingToStates(labelingS1.get(state1), interState, ts);
				addLabelingToStates(labelingS2.get(state2), interState, ts);
				// Add the new state to map of states while Key = S1->S2 value = new state
				Map<S2,Pair<S1,S2>> s2MapForS1LeadsDynamicMap = dynamicMapStatesS1Leads.get(state1);
				if (s2MapForS1LeadsDynamicMap == null) {
					s2MapForS1LeadsDynamicMap = new HashMap<>();
					dynamicMapStatesS1Leads.put(state1, s2MapForS1LeadsDynamicMap);
				}
				s2MapForS1LeadsDynamicMap.put(state2, interState);
				// Add the new state to map of states while Key = S2->S1 value = new state
				Map<S1,Pair<S1,S2>> s1MapForS2LeadsDynamicMap = dynamicMapStatesS2Leads.get(state2);
				if (s1MapForS2LeadsDynamicMap == null) {
					s1MapForS2LeadsDynamicMap = new HashMap<>();
					dynamicMapStatesS2Leads.put(state2, s1MapForS2LeadsDynamicMap);
				}
				s1MapForS2LeadsDynamicMap.put(state1, interState);
			}
		}
	}

	private <S1, S2, S, A, P> void addAtomics(TransitionSystem<S, A, P> tsi, TransitionSystem<Pair<S1, S2>, A, P> ts){
		Set<P> atomicpS = tsi.getAtomicPropositions();
		for (P ap : atomicpS){
			ts.addAtomicProposition(ap);
		}
	}

	private <S1, S2, S, A, P> void addActions(TransitionSystem<S, A, P> tsi, TransitionSystem<Pair<S1, S2>, A, P> ts){
		Set<A> actions = tsi.getActions();
		for (A action : actions){
			ts.addAction(action);
		}
	}

	private <S1, S2, A, P> void handleTranstions1(Set<Transition<S1,A>> ts1_Transtions, Set<Transition> ts1_handShakeTranstions,
			Set<A> handShakingActions, Map<S1, Map<S2,Pair<S1,S2>>> dynamicMapStatesS1Leads, TransitionSystem<Pair<S1, S2>, A, P> ts){
		for (Transition transtion1 : ts1_Transtions) {
			S1 state1From = (S1)transtion1.getFrom();
			S1 state1To = (S1)transtion1.getTo();
			A action1 = (A)transtion1.getAction();
			if(!handShakingActions.contains(action1)){
				Map<S2, Pair<S1, S2>> mapS2KeysPairValsFromState = dynamicMapStatesS1Leads.get(state1From);
				if(mapS2KeysPairValsFromState == null){
					mapS2KeysPairValsFromState = new HashMap<>();
					dynamicMapStatesS1Leads.put(state1From, mapS2KeysPairValsFromState);
				}
				Map<S2, Pair<S1, S2>> mapS2KeysPairValsToState = dynamicMapStatesS1Leads.get(state1To);
				if(mapS2KeysPairValsToState == null){
					mapS2KeysPairValsToState = new HashMap<>();
					dynamicMapStatesS1Leads.put(state1To, mapS2KeysPairValsToState);
				}
				// loop over the map keys in order to generate transitions
				for(S2 state : mapS2KeysPairValsFromState.keySet()){
					Pair<S1,S2> currState = mapS2KeysPairValsFromState.get(state);
					Pair<S1, S2> nextState = mapS2KeysPairValsToState.get(state);
					Transition transitionToAdd = new Transition(currState, action1, nextState);
					ts.addTransition(transitionToAdd);
				}
			}
			else{
				ts1_handShakeTranstions.add(transtion1);
			}
		}
	}

	private <S1, S2, A, P> void handleTranstions2(Set<Transition<S2,A>> ts2_Transtions, Set<Transition> ts2_handShakeTranstions,
			Set<A> handShakingActions, Map<S2, Map<S1,Pair<S1,S2>>> dynamicMapStatesS2Leads, TransitionSystem<Pair<S1, S2>, A, P> ts){
		for (Transition transtion2 : ts2_Transtions) {
			S2 state2From = (S2)transtion2.getFrom();
			S2 state2To = (S2)transtion2.getTo();
			A action2 = (A)transtion2.getAction();
			if(!handShakingActions.contains(action2)) {
				Map<S1, Pair<S1, S2>> mapS1KeysPairValsFromState = dynamicMapStatesS2Leads.get(state2From);
				if(mapS1KeysPairValsFromState == null){
					mapS1KeysPairValsFromState = new HashMap<>();
					dynamicMapStatesS2Leads.put(state2From, mapS1KeysPairValsFromState);
				}
				Map<S1, Pair<S1, S2>> mapS1KeysPairValsToState = dynamicMapStatesS2Leads.get(state2To);
				if(mapS1KeysPairValsToState == null){
					mapS1KeysPairValsToState = new HashMap<>();
					dynamicMapStatesS2Leads.put(state2To, mapS1KeysPairValsToState);
				}
				// loop over the map keys in order to generate transitions
				for(S1 state : mapS1KeysPairValsFromState.keySet()){
					Pair<S1,S2> currState = mapS1KeysPairValsFromState.get(state);
					Pair<S1, S2> nextState = mapS1KeysPairValsToState.get(state);
					Transition transitionToAdd = new Transition(currState, action2, nextState);
					ts.addTransition(transitionToAdd);
				}
			}
			else{
				ts2_handShakeTranstions.add(transtion2);
			}
		}
	}

	private <S1, S2, A, P> void addTransitions(TransitionSystem<S1, A, P> ts1,TransitionSystem<S2, A, P> ts2, Set<A> handShakingActions,
			Map<S1, Map<S2,Pair<S1,S2>>> dynamicMapStatesS1Leads, Map<S2, Map<S1,Pair<S1,S2>>> dynamicMapStatesS2Leads, TransitionSystem<Pair<S1, S2>, A, P> ts){
		Set<Transition<S1,A>> ts1_Transtions = ts1.getTransitions();
		Set<Transition<S2,A>> ts2_Transtions = ts2.getTransitions();
		Set<Transition> ts1_handShakeTranstions = new HashSet<>();
		Set<Transition> ts2_handShakeTranstions = new HashSet<>();
		handleTranstions1(ts1_Transtions, ts1_handShakeTranstions, handShakingActions, dynamicMapStatesS1Leads, ts);
		handleTranstions2(ts2_Transtions, ts2_handShakeTranstions, handShakingActions, dynamicMapStatesS2Leads, ts);
		for (Transition handShake1 : ts1_handShakeTranstions) {
			for (Transition handShake2 : ts2_handShakeTranstions) {
				S1 state1From = (S1)handShake1.getFrom();
				S1 state1To = (S1)handShake1.getTo();
				A action1 = (A)handShake1.getAction();
				S2 state2From = (S2)handShake2.getFrom();
				S2 state2To = (S2)handShake2.getTo();
				A action2 = (A)handShake2.getAction();
				// generate transition only if both transitions have the same action 
				if(action1.equals(action2)){
					Map<S2, Pair<S1, S2>> mapS2KeysPairValsFromState = dynamicMapStatesS1Leads.get(state1From);
					if(mapS2KeysPairValsFromState == null){
						mapS2KeysPairValsFromState = new HashMap<>();
						dynamicMapStatesS1Leads.put(state1From, mapS2KeysPairValsFromState);
					}
					Map<S2, Pair<S1, S2>> mapS2KeysPairValsToState = dynamicMapStatesS1Leads.get(state1To);
					if(mapS2KeysPairValsToState == null){
						mapS2KeysPairValsToState = new HashMap<>();
						dynamicMapStatesS1Leads.put(state1To, mapS2KeysPairValsToState);
					}
					Pair<S1, S2> currState = mapS2KeysPairValsFromState.get(state2From);
					Pair<S1, S2> nextState = mapS2KeysPairValsToState.get(state2To);
					Transition transitionToAdd = new Transition(currState, action1, nextState);
					ts.addTransition(transitionToAdd);
				}
			}
		}
	}

	@Override
	public <S1, S2, A, P> TransitionSystem<Pair<S1, S2>, A, P> interleave(TransitionSystem<S1, A, P> ts1, TransitionSystem<S2, A, P> ts2) {
		return interleave(ts1, ts2, new HashSet<A>());
	}

	@Override
	public <S1, S2, A, P> TransitionSystem<Pair<S1, S2>, A, P> interleave(TransitionSystem<S1, A, P> ts1, TransitionSystem<S2, A, P> ts2, Set<A> handShakingActions) {
		TransitionSystem<Pair<S1, S2>, A, P> ansTs = createTransitionSystem();
		Map<S1, Map<S2,Pair<S1,S2>>> dynamicMapStatesS1Leads = new HashMap<>();
		Map<S2, Map<S1,Pair<S1,S2>>> dynamicMapStatesS2Leads = new HashMap<>();
		addAtomics(ts1, ansTs);
		addAtomics(ts2, ansTs);
		addActions(ts1, ansTs);
		addActions(ts2, ansTs);
		createStatesWithLabeling(ts1, ts2, dynamicMapStatesS1Leads, dynamicMapStatesS2Leads, ansTs);
		addTransitions(ts1, ts2, handShakingActions, dynamicMapStatesS1Leads, dynamicMapStatesS2Leads, ansTs);

		removeUnreachableStates(ansTs);
		return ansTs;
	}

	@Override
	public <L, A> ProgramGraph<L, A> createProgramGraph() {
		return new ProgramGraphImpl<L, A>();
	}

	@Override
	public <L1, L2, A> ProgramGraph<Pair<L1, L2>, A> interleave(ProgramGraph<L1, A> pg1, ProgramGraph<L2, A> pg2) {
		throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement interleave
	}

	private void addToAtomicPropositions(List<String> toAdd, TransitionSystem<Pair<List<Boolean>, List<Boolean>>, List<Boolean>, Object> ts){
		for(int i = 0; i < toAdd.size(); i++){
			ts.addAtomicProposition(toAdd.get(i));
		}
	}

	private void addToLabels(Pair<List<Boolean>, List<Boolean>> state,List<String> toAdd, List<Boolean> toCheck, TransitionSystem<Pair<List<Boolean>, List<Boolean>>, List<Boolean>, Object> ts){
		for(int i = 0; i < toCheck.size(); i++){
			if(toCheck.get(i)){
				ts.addToLabel(state, toAdd.get(i));
			}
		}
	}

	private String convertToBinary(int numToConvert, int length){
		String ans = "";
		for ( int i = 0; i < length; i++,numToConvert /= 2) {
			ans = numToConvert % 2+ans;
		}
		return ans;
	}

	private Set<List<Boolean>> namesToBooleans(List<String> toChange, int n){
		Set<List<Boolean>> ans = new HashSet<>();
		for(int i = 0; i < Math.pow(2,n); i++){
			String stateName = convertToBinary(i,n);
			char[] chars = stateName.toCharArray();
			List<Boolean> lst = new ArrayList<Boolean>();
			for (int j = 0; j < chars.length; j++) {
				lst.add(chars[j] == '0' ? false : true);
			}
			ans.add(lst);
		}

		return ans;
	}

	private void genStatesAndLabels(Circuit cs, TransitionSystem<Pair<List<Boolean>, List<Boolean>>, List<Boolean>, Object> ts,
			List<String> inputsLst, List<String> registersLst, List<String> outputs){
		Set<List<Boolean>> inputs = namesToBooleans(cs.getInputPortNames(), cs.getInputPortNames().size());
		Set<List<Boolean>> registers = namesToBooleans(cs.getRegisterNames(), cs.getRegisterNames().size()); 	
		for(List<Boolean> input : inputs){
			for(List<Boolean> register : registers){
				Pair<List<Boolean>, List<Boolean>> state = new Pair<List<Boolean>, List<Boolean>>(register, input);
				ts.addState(state);
				addToLabels(state, inputsLst, input, ts);
				addToLabels(state, registersLst, register, ts);
				List<Boolean> compOutputs = cs.computeOutputs(register, input);
				addToLabels(state, outputs, compOutputs, ts);
			}
		}
	}

	private void addInitialStateToTs(Set<List<Boolean>> inputsOptions, List<String> registers, TransitionSystem<Pair<List<Boolean>, List<Boolean>>, List<Boolean>, Object> ts){
		for(List<Boolean> lst : inputsOptions){
			List<Boolean> initReg = new ArrayList<Boolean>(Collections.nCopies(registers.size(), false));
			Pair<List<Boolean>, List<Boolean>> initState = new Pair<List<Boolean>, List<Boolean>>(initReg, lst);
			ts.addInitialState(initState);
		}
	}

	private void addActionsToTs(Set<List<Boolean>> inputsOptions, TransitionSystem<Pair<List<Boolean>, List<Boolean>>, List<Boolean>, Object> ts){
		for(List<Boolean> lst : inputsOptions){
			ts.addAction(lst);
		}
	}


	private void addTransitionsToTs(Circuit cs, TransitionSystem<Pair<List<Boolean>, List<Boolean>>, List<Boolean>, Object> ts){
		Set<List<Boolean>> inputs = namesToBooleans(cs.getInputPortNames(), cs.getInputPortNames().size());
		Set<List<Boolean>> registers = namesToBooleans(cs.getRegisterNames(), cs.getRegisterNames().size());
		for (List<Boolean> input : inputs) {
			for (List<Boolean> register : registers) {
				for (List<Boolean> action : inputs) {
					Pair<List<Boolean>, List<Boolean>> fromState = new Pair<List<Boolean>, List<Boolean>>(register, input);
					Pair<List<Boolean>, List<Boolean>> toState = new Pair<List<Boolean>, List<Boolean>>(cs.updateRegisters(register, input) ,action);
					Transition trans = new Transition(fromState, action, toState);
					ts.addTransition(trans);
				}
			}
		}
	}

	@Override
	public TransitionSystem<Pair<List<Boolean>, List<Boolean>>, List<Boolean>, Object> transitionSystemFromCircuit(Circuit c) {
		TransitionSystem<Pair<List<Boolean>, List<Boolean>>, List<Boolean>, Object> ansTs = createTransitionSystem();
		List<String> inputs = c.getInputPortNames();
		List<String> registers = c.getRegisterNames();
		List<String> outputs = c.getOutputPortNames();
		addToAtomicPropositions(inputs, ansTs);
		addToAtomicPropositions(registers, ansTs);
		addToAtomicPropositions(outputs, ansTs);
		genStatesAndLabels(c, ansTs, inputs, registers, outputs);
		Set<List<Boolean>> boolInputs = namesToBooleans(inputs, inputs.size());
		addInitialStateToTs(boolInputs, registers, ansTs);
		addActionsToTs(boolInputs, ansTs);
		addTransitionsToTs(c, ansTs);
		removeUnreachableStates(ansTs);
		return ansTs;
	}

	private <L, A> void buildStates(Set<ActionDef> actionDefs, Set<ConditionDef> conditionDefs, TransitionSystem ts,
			ProgramGraph<L, A> pg, Map<Pair<L, Map<String, Object>>, L> dynamicMapStates){
		Set<PGTransition<L,A>> pgTransitions = pg.getTransitions();
		Set<Pair<L, Map<String, Object>>> currStates = ts.getStates();

		do{
			currStates = ts.getStates();
			for(Pair<L, Map<String, Object>> state : currStates){
				for(PGTransition pgTransition : pgTransitions){
					L fromState = (L)pgTransition.getFrom();
					L toState = (L)pgTransition.getTo();
					A action = (A)pgTransition.getAction();
					String cond = pgTransition.getCondition();
					if(fromState.equals(dynamicMapStates.get(state))){
						if(evaluate(conditionDefs, state.getSecond(), cond)){
							Map<String, Object> eval = new LinkedHashMap<>();
							eval = ActionDef.effect(actionDefs, state.getSecond(), action);
							if (eval != null){
								Pair<L, Map<String, Object>> buildState = new Pair<L, Map<String, Object>>(toState, eval);
								ts.addAction(action);
								ts.addState(buildState);
								ts.addAtomicProposition(toState);
								ts.addToLabel(buildState,toState);
								dynamicMapStates.put(buildState,toState);
								Transition t = new Transition(state, action, buildState);
								ts.addTransition(t);
								for(Map.Entry<String, Object> mapEntry : eval.entrySet())
								{
									String atomic = mapEntry.getKey() + " = " + mapEntry.getValue();
									ts.addAtomicProposition(atomic);
									ts.addToLabel(buildState,atomic);
								}
							}
						}
					}
				}
			}
		}while(!ts.getStates().equals(currStates));
	}

	private <L, A> void createInitialStates(Set<ActionDef> actionDefs, Set<ConditionDef> conditionDefs, TransitionSystem ts,
			ProgramGraph<L, A> pg, Map<Pair<L, Map<String, Object>>, L> dynamicMapStates, L loc){
		//Set<L> initLocations = pg.getInitialLocations();
		Set<List<String>> initializationsSet = pg.getInitalizations();
		//for(L loc : initLocations){
		for(List<String> initializations : initializationsSet) {
			Map<String, Object> eval = new LinkedHashMap<>();
			for(String init : initializations)
			{
				eval = ActionDef.effect(actionDefs, eval, init);
			}

			Pair<L, Map<String, Object>> buildState = new Pair<L, Map<String, Object>>(loc, eval);
			ts.addState(buildState);
			ts.addInitialState(buildState);
			ts.addAtomicProposition(loc);
			ts.addToLabel(buildState,loc);
			dynamicMapStates.put(buildState,loc);
			for(Map.Entry<String, Object> mapEntry : eval.entrySet())
			{
				String atomic = mapEntry.getKey() + " = " + mapEntry.getValue();
				ts.addAtomicProposition(atomic);
				ts.addToLabel(buildState,atomic);
			}
		}
		//}
	}

	private <L, A> void createInitialStateWhileEmptyInitList(Set<ActionDef> actionDefs, Set<ConditionDef> conditionDefs, TransitionSystem ts, 
			ProgramGraph<L, A> pg, Map<Pair<L, Map<String, Object>>, L> dynamicMapStates, L loc){
		//Set<L> initLocations = pg.getInitialLocations();
		//for (L loc : initLocations){
		Map<String, Object> mapVarToVAlForState = new HashMap<String, Object>();
		Pair<L, Map<String, Object>> buildState = new Pair(loc, mapVarToVAlForState);
		ts.addState(buildState);
		ts.addInitialState(buildState);
		ts.addToLabel(buildState,loc);
		ts.addAtomicProposition(loc);
		dynamicMapStates.put(buildState,loc);
		//}    
	}

	@Override
	public <L, A> TransitionSystem<Pair<L, Map<String, Object>>, A, String> transitionSystemFromProgramGraph(ProgramGraph<L, A> pg, Set<ActionDef> actionDefs, Set<ConditionDef> conditionDefs) {
		TransitionSystem<Pair<L, Map<String, Object>>, A, String> ansTs = createTransitionSystem();
		Map<Pair<L, Map<String, Object>>, L> dynamicMapStates = new HashMap<>();
		Set<L> initLocations = pg.getInitialLocations();
		for (L loc : initLocations){
			if(pg.getInitalizations().isEmpty()){
				createInitialStateWhileEmptyInitList(actionDefs,conditionDefs, ansTs, pg, dynamicMapStates, loc);
			}
			createInitialStates(actionDefs, conditionDefs ,ansTs , pg, dynamicMapStates, loc);
		}
		buildStates(actionDefs, conditionDefs, ansTs, pg, dynamicMapStates);
		removeUnreachableStates(ansTs);
		return ansTs;
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
