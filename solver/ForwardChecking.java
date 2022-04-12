package solver;
import java.util.HashMap;
import java.sql.Time;
import java.util.ArrayList;
import java.util.Collections;
import representations.*;

/*
foreach(d in Depth):
    assign(xdepth,d)
    consistent = true
    for future = depth + 1 to n while consistent
        consistent = revise(arc(xfuture,xdepth))
    if(consistent)
        if(depth = n)
            showSolution()
        else this(depth + 1)
    undo pruning
*/
public class ForwardChecking implements Solver {
  
  private ArrayList<Integer> variableList = new ArrayList<>();
  private ArrayList<Integer> assignedVars = new ArrayList<>();
  private BinaryCSP binaryCSP;
  private ArrayList<BinaryConstraint> binaryConstraints;
  private HashMap<Integer, ArrayList<Integer>> domains = new HashMap<>(); //map a variable to its given domain via a hashmap 
  private TimeManager timeManager;
  private boolean solution = false;

  public ForwardChecking(BinaryCSP binaryCSP, TimeManager manager) {
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
      forwardChecking(variableList);
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
   * main forward checking algorithm
   * @param variableList
   */
  private void forwardChecking( ArrayList<Integer> variableList) {
    if(!solution && assignedVars.size() == binaryCSP.getNoVariables()) {
        solution = true;
        System.out.println("solution found");
        timeManager.stop();
        printSolution();
    }
    else if(!solution) {
        int variable = getNextVariable(variableList);
        int value = getNextValue(variable);
        reviseArcFuture(variable, value, variableList);
        reviseArcDepth(variable, value, variableList);
    }
  }
/**
 * revise arc(xfuture) : half of the recursive procedure
 * @param variable
 * @param value
 * @param variableList
 */
  private void reviseArcFuture(int variable, int value, ArrayList<Integer> variableList) {
    HashMap<Integer, ArrayList<Integer>> newDomains = (HashMap<Integer, ArrayList<Integer>>) domains.clone();
    assignVariablePruneDomain(variable, value);
    if(CheckAllArcs(variableList,variable)) {
      forwardChecking(getUnassignedVariables());//call the main algorithm with the variable assigned
    }
    domains = newDomains;
    deAssignVariable(variable);//undo the prune
  }
/**
 * revise arc(xdepth): the other half of the recursion
 * @param variable
 * @param value
 * @param variableList
 */
  private void reviseArcDepth(int variable, int value, ArrayList<Integer> variableList) {
    deleteValueVariableDomain(variable, value);
    HashMap<Integer, ArrayList<Integer>> newDomains = (HashMap<Integer, ArrayList<Integer>>) domains.clone();
    if(!domains.get(variable).isEmpty()) {
      if(CheckAllArcs( variableList,variable)) {
          forwardChecking(variableList);
        }
      domains = newDomains;
    }
    addValueVariableDomain(variable, value);
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
 * returns true if all arcs are consistent 
 * @param variableList
 * @param variable
 * @return
 */
	private boolean CheckAllArcs(ArrayList<Integer> variableList, int variable) {
		for(int futureVariable : variableList) {
			if(futureVariable != variable) {
				if(!checkArc(variable, futureVariable))
					return false;
			}
		}
		return true;
	}
/**
 * prunes a domain, returns true upon success
 * @param variable
 * @param futureVariable
 * @return
 */	
	private boolean checkArc(int variable, int futureVariable) {
		ArrayList<Integer> correctValues = getValuesSatisfyingConstraints(variable, futureVariable); 
		ArrayList<Integer> newDomain = (ArrayList<Integer>) domains.get(futureVariable).clone();	
		for(int i = 0; i < domains.get(futureVariable).size(); i++) {
			if(!correctValues.contains(domains.get(futureVariable).get(i))) {	
				newDomain.remove(newDomain.indexOf(domains.get(futureVariable).get(i)));	
			}
		}
		domains.put(futureVariable, newDomain);	
    return !newDomain.isEmpty();
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