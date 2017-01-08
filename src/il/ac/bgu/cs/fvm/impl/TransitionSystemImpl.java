package il.ac.bgu.cs.fvm.impl;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import il.ac.bgu.cs.fvm.exceptions.ActionNotFoundException;
import il.ac.bgu.cs.fvm.exceptions.DeletionOfAttachedActionException;
import il.ac.bgu.cs.fvm.exceptions.DeletionOfAttachedAtomicPropositionException;
import il.ac.bgu.cs.fvm.exceptions.DeletionOfAttachedStateException;
import il.ac.bgu.cs.fvm.exceptions.FVMException;
import il.ac.bgu.cs.fvm.exceptions.InvalidInitialStateException;
import il.ac.bgu.cs.fvm.exceptions.InvalidLablingPairException;
import il.ac.bgu.cs.fvm.exceptions.InvalidTransitionException;
import il.ac.bgu.cs.fvm.exceptions.StateNotFoundException;
import il.ac.bgu.cs.fvm.exceptions.TransitionSystemPart;
import il.ac.bgu.cs.fvm.transitionsystem.Transition;
import il.ac.bgu.cs.fvm.transitionsystem.TransitionSystem;

public class TransitionSystemImpl<STATE, ACTION, ATOMIC_PROPOSITION> implements TransitionSystem<STATE, ACTION, ATOMIC_PROPOSITION> {

/******************************
 	**** Private members ****
 ******************************/
	String tsName;
	Set<STATE>	states;
	Set<STATE>	initStates;
	Set<ACTION> actions;
	Set<Transition<STATE,ACTION>> transitions;
	Set<ATOMIC_PROPOSITION> ap;
	Map<STATE, Set<ATOMIC_PROPOSITION>> taggedStates;

/******************************
	**** Constructors ****
 ******************************/
	
	public TransitionSystemImpl(){
		tsName = "";
		states = new HashSet<STATE>();
		initStates = new HashSet<STATE>();
		actions = new HashSet<ACTION>();
		transitions = new HashSet<Transition<STATE,ACTION>>();
		ap = new HashSet<ATOMIC_PROPOSITION>();
		taggedStates = new HashMap<STATE, Set<ATOMIC_PROPOSITION>>();
	}
	
/******************************
 	**** Public methods ****
 ******************************/

	@Override
	public String getName() {
		return tsName;
	}

	@Override
	public void setName(String name) {
		tsName = name;
	}

	@Override
	public void addAction(ACTION action) {
		actions.add(action);
	}

	@Override
	public void addInitialState(STATE state) throws FVMException {
		if(states.contains(state))
			initStates.add(state);
		else throw new InvalidInitialStateException(state);	
	}

	@Override
	public void addState(STATE state) {
		states.add(state);
		HashSet<ATOMIC_PROPOSITION> tags = new HashSet<ATOMIC_PROPOSITION>();
		taggedStates.put(state, tags);
	}

	@Override
	public void addTransition(Transition<STATE, ACTION> t) throws FVMException {
			boolean containsFrom = states.contains(t.getFrom());
			boolean containsTo = states.contains(t.getTo());
			boolean containsAction = actions.contains(t.getAction());
			if(containsFrom && containsTo && containsAction)
				transitions.add(t);
			else
				throw new InvalidTransitionException(t);
	}

	@Override
	public Set<ACTION> getActions() {
		return actions;
	}

	@Override
	public void addAtomicProposition(ATOMIC_PROPOSITION p) {
		ap.add(p);
	}

	@Override
	public Set<ATOMIC_PROPOSITION> getAtomicPropositions() {
		return ap;
	}

	@Override
	public void addToLabel(STATE s, ATOMIC_PROPOSITION l) throws FVMException {
		boolean containState = states.contains(s);
		boolean containsAP = ap.contains(l);
		if(containState && containsAP)
			taggedStates.get(s).add(l);
		else throw new InvalidLablingPairException(s, l);
	}

	@Override
	public Set<ATOMIC_PROPOSITION> getLabel(STATE s) {
		if(states.contains(s))
			return taggedStates.get(s);
		else throw new StateNotFoundException(s);
	}

	@Override
	public Set<STATE> getInitialStates() {
		return initStates;
	}

	@Override
	public Map<STATE, Set<ATOMIC_PROPOSITION>> getLabelingFunction() {
		return taggedStates;
	}

	@Override
	public Set<STATE> getStates() {
		return states;
	}

	@Override
	public Set<Transition<STATE, ACTION>> getTransitions() {
		return transitions;
	}

	@Override
	public void removeAction(ACTION action) throws FVMException {
		boolean actionsContains = actions.contains(action);
		if(!actionsContains)
			throw new ActionNotFoundException(action);
		for (Transition t : transitions) {
			if(t.getAction().equals(action)){
				throw new DeletionOfAttachedActionException(action, TransitionSystemPart.ACTIONS);
			}
		}
		actions.remove(action);
	}

	@Override
	public void removeAtomicProposition(ATOMIC_PROPOSITION p) throws FVMException {
		boolean isTagExists = false;
		Set<ATOMIC_PROPOSITION> tags;
		for (STATE s : taggedStates.keySet()) {
			if(isTagExists)
				break;
			tags = taggedStates.get(s);
			isTagExists = tags.contains(p);
		}
		if(isTagExists)
			throw new DeletionOfAttachedAtomicPropositionException(p, TransitionSystemPart.ATOMIC_PROPOSITIONS);
		else ap.remove(p);
	}

	@Override
	public void removeInitialState(STATE state) {
		initStates.remove(state);
	}

	@Override
	public void removeLabel(STATE s, ATOMIC_PROPOSITION l) {
		Set<ATOMIC_PROPOSITION> oldTags = taggedStates.get(s);
		oldTags.remove(l);
		Set<ATOMIC_PROPOSITION> newTags = new HashSet<ATOMIC_PROPOSITION>(oldTags);
		taggedStates.put(s, newTags);
	}

	@Override
	public void removeState(STATE state) throws FVMException {
		boolean isStateTagged  = !taggedStates.get(state).isEmpty();
		boolean isInitState = initStates.contains(state);
		for (Transition t : transitions) {
			if(t.getFrom().equals(state) || t.getTo().equals(state)){
				throw new DeletionOfAttachedStateException(state, TransitionSystemPart.TRANSITIONS);
			}
		}
		if(isInitState)
			throw new DeletionOfAttachedStateException(state,TransitionSystemPart.INITIAL_STATES);
		else if(isStateTagged)
			throw new DeletionOfAttachedStateException(state,TransitionSystemPart.ATOMIC_PROPOSITIONS);
		else states.remove(state);
	}

	@Override
	public void removeTransition(Transition<STATE, ACTION> t) {
		transitions.remove(t);
	}
}
