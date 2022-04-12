package solver;
import java.util.HashMap;

import representations.BinaryConstraint;
import representations.BinaryCSP;
import representations.BinaryTuple;

import java.util.ArrayList;
import java.util.Collections;
/*
Procedure MAC3(varList)
    variable = selectVar(VarList)
    value = selectVal(domain(variable))
    assign(variable,value)
    if(complete assignment)
        show solution
    else if (AC3())
        MAC3(varlist-variable)
    undoPruning()
    unassign(variable,value)
    remove value from domain(variable)
    if (not(empty(domain(variable))))
        if(AC3())
            MAC3(varList)
        undoPruning()
    replace value in domain(variable)
 */
public class ArcConsistency implements Solver {
  private ArrayList<Integer> variableList = new ArrayList<>();
  private ArrayList<Integer> assignedVars = new ArrayList<>();
  private BinaryCSP binaryCSP;
  private ArrayList<BinaryConstraint> binaryConstraints;
  private HashMap<Integer, ArrayList<Integer>> domains = new HashMap<>(); //map a variable to it's given domain via a hashmap 
  private boolean solutionFound = false;
  private TimeManager timeManager;

  public ArcConsistency(BinaryCSP binaryCSP, TimeManager manager) {
    this.binaryCSP = binaryCSP;
    this.binaryConstraints = binaryCSP.getConstraints();
    this.timeManager = manager;
    //initialise the hashmap of variable domain pairs by inspecting each variable in the csp object
    for(int i = 0; i < binaryCSP.getNoVariables(); i++) {
        ArrayList<Integer> domain = new ArrayList<>();
        for(int j = binaryCSP.getLB(i); j <= binaryCSP.getUB(i); j++) {
            domain.add(j);
        }
        variableList.add(i);
        this.domains.put(i, domain);
    }
  }        
  /**
   * runs the forward checking algorithm and begins the recursion
   */
  public void run() {
      timeManager.start();
      MAC3(variableList);
  }
  /**
   * print the solution to the csp
   */
  private void printSolution() {
    for (int variable : domains.keySet()) {
            System.out.println(variable + " " + domains.get(variable));
    }
    System.out.println("Time taken: " + timeManager.getElapsedTime());
  }
  /**
   * maintaining arc consistency algorithm
   * 
   * @param variableList
   */
  private void MAC3(ArrayList<Integer> variableList) {
    int variable = getNextVariable(variableList);
    int value = getNextValue(variable);		
    HashMap<Integer, ArrayList<Integer>> prevDomains = (HashMap<Integer, ArrayList<Integer>>) domains.clone();
    assignVariablePruneDomain(variable, value);//prune domain when we assign variable	
    if(assignedVars.size() == binaryCSP.getNoVariables() && !solutionFound) {
        timeManager.stop();
        printSolution();
        solutionFound = true;
    }
    else if(AC3(variable) && !solutionFound) {
        variableList = getUnassignedVariables();
        MAC3(variableList);
    }
    //undo pruning 
    domains = prevDomains;
    deAssignVariable(variable); 
    deleteValueVariableDomain(variable, value);
    prevDomains = (HashMap<Integer, ArrayList<Integer>>) domains.clone();
    if(!domains.get(variable).isEmpty()) {
        if(AC3(variable))
            MAC3(variableList);
        else
            domains = prevDomains;
    }
    addValueVariableDomain(variable, value);		
  }
/**
 * AC3 algorithm, puts arcs inside a fifo queue, then checks if they maintain consistency
 * @param variable
 * @return
 */
  private boolean AC3(int variable) {
    ArrayList<int[]> consistencyQueue = new ArrayList<>();
    for(BinaryConstraint constraint : binaryConstraints) {
        if(constraint.getFirstVar() == variable && !assignedVars.contains(constraint.getSecondVar())){
            int[] arc = new int[2];
            arc[0] = variable;
            arc[1] = constraint.getSecondVar();
            consistencyQueue.add(arc);
        }
    }
    while(!consistencyQueue.isEmpty()) {
      int[] arc = consistencyQueue.get(0);
      consistencyQueue.remove(0);
      try {
        if(checkArc(arc[0], arc[1])) { 
          for(BinaryConstraint constraint : binaryConstraints) {
            if(constraint.getFirstVar() == arc[1]) {
              int[] newArc = {arc[1], constraint.getSecondVar()};
              consistencyQueue.add(newArc);
            }
          }
        }
      }
      catch(IndexOutOfBoundsException e) {
        return false;
      }
    }
    return true;
  }
/**
 * return the variables that have not been assigned at this moment
 * @return
 */
  private ArrayList<Integer> getUnassignedVariables() {
    ArrayList<Integer> unassignedVariables = new ArrayList<>();
    for(int i = 0; i < binaryCSP.getNoVariables(); i++) {
      if(!assignedVars.contains(i)){
        unassignedVariables.add(i);
      }
    }
    return unassignedVariables;
  }
/**
 * given a list of variables, return the one with the smallest domain to be recursed next
 * @param variableList
 * @return an integer denoting a variable
 */
  private int getNextVariable(ArrayList<Integer> variableList) {
    int output = variableList.get(0); 
    int minDomain = Integer.MAX_VALUE; 
    if(!(variableList.size() == binaryCSP.getNoVariables())){
      for(int variable : variableList) {
        if(domains.get(variable).size() < minDomain) {
          minDomain = domains.get(variable).size();
          output = variable;
        }
      }
    }
    return output;
  }
  /** 
   * Given a variable, return the next value from its domain, invalid domain values are removed before this function call
   * @param variable
   * @return domain value to be checked
   */
  private int getNextValue(int variable) {
    ArrayList<Integer> varDomain = domains.get(variable);
    Collections.sort(varDomain);
    return varDomain.get(0);
  }
  /**
   * given a variable and a domain value, remove every other domain value and set it as assigned for relevant checking 
   * @param variable
   * @param value
   */
  private void assignVariablePruneDomain(int variable, int value) {
    ArrayList<Integer> newDomain = new ArrayList<>();
    newDomain.add(value);
    assignedVars.add(variable);
    domains.put(variable, newDomain);
  }
  private void deAssignVariable(int variable) {
    assignedVars.remove(assignedVars.indexOf(variable));
  }
  /**
   * given a variable, add a given value to its domain
   * @param variable
   * @param value
   */
  private void addValueVariableDomain(int variable, int value) {
    ArrayList<Integer> newDomain = new ArrayList<>();
    newDomain = domains.get(variable);
    newDomain.add(value);
    domains.put(variable, newDomain);
  }
  /**
   * given a variable, remove a value from its domain
   * @param variable
   * @param value
   */
  private void deleteValueVariableDomain(int variable, int value) {
    ArrayList<Integer> newDomain = new ArrayList<>();
    newDomain = domains.get(variable);
    newDomain.remove(newDomain.indexOf(value));
    domains.put(variable, newDomain);
  }

/**
 * prunes a domain, returns true upon success
 * @param variable
 * @param futureVariable
 * @return
 */	
	private boolean checkArc(int variable, int futureVariable) throws IndexOutOfBoundsException {
		boolean output = false;
		ArrayList<Integer> satisfyingValues = getValuesSatisfyingConstraints(variable, futureVariable); 
		ArrayList<Integer> newDomain = (ArrayList<Integer>) domains.get(futureVariable).clone(); 
		for(int i = 0; i < domains.get(futureVariable).size(); i++) {
			if(!satisfyingValues.contains(domains.get(futureVariable).get(i))) {
				output = true;
				newDomain.remove(newDomain.indexOf(domains.get(futureVariable).get(i)));
			}
		}
		domains.put(futureVariable, newDomain);
		if(newDomain.isEmpty()){
			throw new IndexOutOfBoundsException();
    }
		return output;
	}
/**
 * return all of the values that satisfy the constraints for a given variable
 * @param variable
 * @param futureVariable
 * @return
 */
	private ArrayList<Integer> getValuesSatisfyingConstraints(int variable, int futureVariable) {
		ArrayList<Integer> output = new ArrayList<>();
		for(BinaryConstraint constraint : binaryConstraints) {
			if(constraint.getFirstVar() == variable && constraint.getSecondVar() == futureVariable) {
				for(BinaryTuple binaryTuple : constraint.getBinaryTuples()) {
					for(int value : domains.get(variable)) {
						if(binaryTuple.getVal1() == value) {
							output.add(binaryTuple.getVal2());
						}
					}
				}
			}
		}
		return output;
	}
}
