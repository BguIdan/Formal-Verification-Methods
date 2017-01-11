package il.ac.bgu.cs.fvm.impl;

import java.util.HashSet;
import java.util.List;
import java.util.Set;

import il.ac.bgu.cs.fvm.programgraph.PGTransition;
import il.ac.bgu.cs.fvm.programgraph.ProgramGraph;

public class ProgramGraphImpl<L, A> implements ProgramGraph<L, A> {

/******************************
 	**** Private members ****
 ******************************/
	String pgName;
	Set<List<String>> initialList; 
	Set<L> locations;
	Set<L> initLocations;
	Set<A> actions;
	Set<PGTransition<L,A>> pgTransitions;

/******************************
	**** Constructors ****
 ******************************/
	public ProgramGraphImpl() {
		this.pgName = "";
		this.initialList = new HashSet<>();
		this.locations = new HashSet<L>();
		this.initLocations = new HashSet<L>();
		this.actions = new HashSet<A>();
		this.pgTransitions = new HashSet<PGTransition<L, A>>();
	}
	
	
/******************************
 	**** Public methods ****
 ******************************/
	@Override
	public void addInitalization(List<String> init) {
		initialList.add(init);
		
	}

	@Override
	public void addInitialLocation(L location) {
		initLocations.add(location);		
	}

	@Override
	public void addLocation(L l) {
		locations.add(l);
	}

	@Override
	public void addTransition(PGTransition<L, A> t) {
		pgTransitions.add(t);
	}

	@Override
	public Set<List<String>> getInitalizations() {
		return new HashSet<>(initialList);
	}

	@Override
	public Set<L> getInitialLocations() {
		return new HashSet<>(initLocations);
	}

	@Override
	public Set<L> getLocations() {
		return new HashSet<>(locations);
	}

	@Override
	public String getName() {
		return pgName;
	}

	@Override
	public Set<PGTransition<L, A>> getTransitions() {
		return new HashSet<>(pgTransitions);
	}

	@Override
	public void removeLocation(L l) {
		locations.remove(l);
	}

	@Override
	public void removeTransition(PGTransition<L, A> t) {
		pgTransitions.remove(t);
	}

	@Override
	public void setName(String name) {
		pgName = name;
	}

}
