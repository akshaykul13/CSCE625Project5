import java.io.File;
import java.io.FileNotFoundException;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.Scanner;


public class PropositionalSatisfiabillitySolver {
	
	private static ArrayList<Clause> knowledgeBase;
	private static int numberOfClauses = 0;
	private static int count = 0;
	private static int MODE;
	private static boolean MINIMALISTIC_ALGORITHM = false;
	
	private static final int ONLY_BACKTRACKING = 1;
	private static final int BACKTRACKING_WITH_UNIT_CLAUSE = 2;
	private static final int BACKTRACKING_WITH_UNIT_AND_PURE = 3;
	
	public static void main(String[] args) {
		knowledgeBase = new ArrayList<Clause>();
		ArrayList<String> symbols = new ArrayList<String>();
		HashMap<String, Boolean> model = new HashMap<String, Boolean>();
		String fileName = args[0];		
		MODE = Integer.parseInt(args[1]);
		if(MODE == 1) {
			System.out.println("Only Backtracking");
		} else if(MODE == 2) {
			System.out.println("Backtracking with unit clause heuristic");
		} else if(MODE == 3) {
			System.out.println("Backtracking with unit and pure clause heuristics");
		} else {
			System.out.println("Invalid mode");
			System.exit(-1);
		}
		if(args.length == 3) {
			if(args[2].equals("-m")) {
				MINIMALISTIC_ALGORITHM = true;
				System.out.println("Minimalistic mode");
			}
		}
		ArrayList<String> facts = new ArrayList<String>();
		Scanner in = new Scanner(System.in);			
		System.out.println("Enter additional propositional facts:");
		while(in.hasNextLine()) {
			String fact = in.nextLine();
			if(fact.isEmpty()) {
				break;
			}
			facts.add(fact);
		}
		in.close();
		extractKnowledgeBase(fileName, symbols, facts);
		Collections.sort(symbols);
		DPLL(symbols, model);		
	}
	
	private static boolean DPLL(ArrayList<String> symbols, HashMap<String, Boolean> model) {
		System.out.println("DPLL on " + model.toString());
		count++;
		if(allClausesAreTrue(model)) {
			System.out.println();
			ArrayList<String> keys = new ArrayList<String>(model.keySet());		
			Collections.sort(keys);
			for (String key : keys) {
				System.out.println(key + ": " + model.get(key));
			}
			System.out.println("Node searched = " + count);
			System.exit(0);
		}
		if(someClauseIsFalse(model)) {
			return false;
		}
		if (MODE == BACKTRACKING_WITH_UNIT_AND_PURE) {
			String pureSymbol = findPureSymbol(symbols, model);
			if(pureSymbol != null) {
				boolean isNegative = pureSymbol.startsWith("-");
				String symbol = pureSymbol.startsWith("-") ? pureSymbol.substring(1) : pureSymbol;
				HashMap<String, Boolean> newModel = (HashMap)model.clone();
				ArrayList<String> newSymbols = cloneList(symbols);
				newModel.put(symbol, !isNegative);
				newSymbols.remove(symbol);
				return DPLL(newSymbols, newModel);
			}
		}			
		if (MODE == BACKTRACKING_WITH_UNIT_CLAUSE || MODE == BACKTRACKING_WITH_UNIT_AND_PURE) {
			String unitClause = findUnitClause(symbols, model);
			if(unitClause != null) {
				boolean isNegative = unitClause.startsWith("-");
				String symbol = unitClause.startsWith("-") ? unitClause.substring(1) : unitClause;
				HashMap<String, Boolean> newModel = (HashMap)model.clone();
				ArrayList<String> newSymbols = cloneList(symbols);
				newModel.put(symbol, !isNegative);
				newSymbols.remove(symbol);
				return DPLL(newSymbols, newModel);
			}	
		}		
		String symbolToBeAssigned = symbols.get(0);
		HashMap<String, Boolean> newModel = (HashMap)model.clone();
		ArrayList<String> newSymbols = cloneList(symbols);
		newSymbols.remove(0);
		System.out.println("Assigning symbol - " + symbolToBeAssigned);
		newModel.put(symbolToBeAssigned, !MINIMALISTIC_ALGORITHM);		
		boolean flag = DPLL(newSymbols, newModel);
		if(!flag) {
			newModel.put(symbolToBeAssigned, MINIMALISTIC_ALGORITHM);
			flag = DPLL(newSymbols, newModel);
		}				
		return flag;
	}

	private static String findPureSymbol(ArrayList<String> symbols, HashMap<String, Boolean> model) {
		for (String symbol : symbols) {
			String symbolObserverd = null;
			boolean isPureSymbol = true;
			for (Clause clause : knowledgeBase) {
				if(clause.getLiterals().contains(symbol)) {
					if(symbolObserverd != null && !symbolObserverd.equals(symbol)) {
						isPureSymbol = false;
						break;
					} else {
						symbolObserverd = symbol;
					}
				} else if(clause.getLiterals().contains("-" + symbol)) {
					if(symbolObserverd != null && !symbolObserverd.equals("-" + symbol)) {
						isPureSymbol = false;
						break;
					} else {
						symbolObserverd = "-" + symbol;
					}
				}
			}
			if(isPureSymbol) {
				System.out.println("Found pure symbol - " + symbolObserverd);
				return symbolObserverd;
			}
		}
		return null;
	}

	private static ArrayList<String> cloneList(ArrayList<String> symbols) {		
		ArrayList<String> clone = new ArrayList<String>();
		for (String symbol : symbols) {
			clone.add(symbol);
		}
		return clone;			
	}

	private static String findUnitClause(ArrayList<String> symbols, HashMap<String, Boolean> model) {
		for (Clause clause : knowledgeBase) {
			int unassignedLiteralCount = 0;
			String unassignedLiteral = null;
			boolean isClauseTrue = false;
			for (String literal : clause.getLiterals()) {
				boolean isNegative = literal.startsWith("-");
				String symbol = literal.startsWith("-") ? literal.substring(1) : literal;
				if(!model.keySet().contains(symbol)) {
					unassignedLiteralCount++;
					unassignedLiteral = literal;
				} else {
					if((isNegative && !model.get(symbol)) || (!isNegative && model.get(symbol))) {
						isClauseTrue = true;
					}
				}
			}
			if(unassignedLiteralCount == 1 && !isClauseTrue) {
				System.out.println("Found unit clause - " + unassignedLiteral);
				return unassignedLiteral;
			}
		}
		return null;
	}

	private static boolean someClauseIsFalse(HashMap<String, Boolean> model) {
		for (Clause clause : knowledgeBase) {
			boolean allSymbolsAssigned = true;
			for (String literal : clause.getLiterals()) {
				String symbol = literal.startsWith("-") ? literal.substring(1) : literal;
				if (!model.keySet().contains(symbol)) {
					allSymbolsAssigned = false;					
				}
			}
			if(allSymbolsAssigned && !isClauseTrue(clause, model)) {
				return true;
			}
		}
		return false;
	}

	private static boolean allClausesAreTrue(HashMap<String, Boolean> model) {		
		for (Clause clause : knowledgeBase) {
			for (String literal : clause.getLiterals()) {
				String symbol = literal.startsWith("-") ? literal.substring(1) : literal;
				if (!model.keySet().contains(symbol)) {
					return false;					
				}
			}
			if(!isClauseTrue(clause, model)) {
				return false;
			}
		}
		return true;
	}

	private static boolean isClauseTrue(Clause clause, HashMap<String, Boolean> model) {		
		for (String literal : clause.getLiterals()) {
			boolean isNegative = literal.startsWith("-");
			String symbol = literal.startsWith("-") ? literal.substring(1) : literal;
			if ((isNegative && !model.get(symbol)) || (!isNegative && model.get(symbol))) {
				return true;
			} 
		}
		return false;
	}

	private static void extractKnowledgeBase(String fileName, ArrayList<String> symbols, ArrayList<String> facts) {
		File knowledgeBaseFile = new File(fileName);
		try {
			Scanner in = new Scanner(knowledgeBaseFile);
			while(in.hasNext()) {
				String clauseText = in.nextLine();
				if(clauseText.startsWith("#") || clauseText.isEmpty()) {					
					continue;
				}
				Clause clause = new Clause(clauseText, numberOfClauses);
				knowledgeBase.add(clause);
				extractSymbols(clause, symbols);
				numberOfClauses++;
			}
			in.close();
			for (String fact : facts) {
				String clauseText = fact;				
				Clause clause = new Clause(clauseText, numberOfClauses);
				knowledgeBase.add(clause);
				extractSymbols(clause, symbols);
				numberOfClauses++;
			}			
		} catch (FileNotFoundException e) {
			e.printStackTrace();
			System.out.println("Place the input file in the folder which contains src and bin if running from eclipse");
			System.out.println("Place the input file in the bin folder if running from command line");
			System.exit(-1);
		}
		
	}

	private static void extractSymbols(Clause clause, ArrayList<String> symbols) {		
		for (String s : clause.getLiterals()) {
			String symbol = s;
			if(s.startsWith("-")) {
				symbol = symbol.substring(1);
			}
			if(!symbols.contains(symbol)) {
				symbols.add(symbol);
			}			
		}
	}
}
