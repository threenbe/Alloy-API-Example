package pset1;

/*
 * Derived from edu.mit.csail.sdg.alloy4whole.ExampleUsingTheCompiler.java
 * http://alloy.mit.edu/alloy/code/ExampleUsingTheCompiler.java
 *
 */

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4.SafeList;
import edu.mit.csail.sdg.alloy4compiler.ast.Command;
import edu.mit.csail.sdg.alloy4compiler.ast.Module;
import edu.mit.csail.sdg.alloy4compiler.ast.Sig;
import edu.mit.csail.sdg.alloy4compiler.ast.Sig.Field;
import edu.mit.csail.sdg.alloy4compiler.parser.CompUtil;
import edu.mit.csail.sdg.alloy4compiler.translator.A4Options;
import edu.mit.csail.sdg.alloy4compiler.translator.A4Solution;
import edu.mit.csail.sdg.alloy4compiler.translator.A4Tuple;
import edu.mit.csail.sdg.alloy4compiler.translator.A4TupleSet;
import edu.mit.csail.sdg.alloy4compiler.translator.TranslateAlloyToKodkod;

public class ExampleUsingAlloyAPI {
	final static String PATH = "";

	public static void main(String[] args) throws Err {
		String filename = PATH + "typehierarchy.als";
		A4Reporter rep = new A4Reporter();
		
		// Parse+typecheck the model
		System.out.println("=========== Parsing+Typechecking "+filename+" =============");
		Module world = CompUtil.parseEverything_fromFile(rep, null, filename);
		
		// Set options for how to execute the command
		A4Options options = new A4Options();
		options.solver = A4Options.SatSolver.SAT4J;
		
		Command command = world.getAllCommands().get(0);
		System.out.println("============ Command "+command+": ============");
		
		// generate and store all solutions
		List<A4Solution> allSols = new ArrayList<A4Solution>();
		int count = findAllSols(rep, world, options, command, allSols);
		System.out.println("number of solutions: " + count);
		
		// translate each solution into the corresponding Java program
		System.out.println("-----------");
		for (A4Solution sol: allSols) {
			String program = createProgram(sol,
					getRelation(sol, "Type", "ext"),
					getRelation(sol, "Class", "impl"));
			System.out.print(program);
			System.out.println("-----------");
		}
	}
	
	private static int findAllSols(A4Reporter rep, Module world,
		A4Options options, Command command, List<A4Solution> allSols) throws Err {
			// execute the given command using TranslateAlloyToKodkod.execute_command(...)
			// add each solution found to allSols in order
			// return the number of solutions found
			// hint: study the implementations of
			// edu.mit.csail.sdg.alloy4whole.ExampleUsingTheCompiler.java and
			// EvaluatorExample at http://alloy.mit.edu/alloy/alloy-api-examples.html
			
			// your code goes here
		
		A4Solution sol = TranslateAlloyToKodkod.execute_command(rep, world.getAllReachableSigs(), command, options);
		while (sol.satisfiable()) {
			//System.out.println(sol);
			allSols.add(sol);
			sol = sol.next();
		}
		return allSols.size();
	}
	
	private static Map<String, String> getRelation(A4Solution sol,
			String signame, String fieldname) {
			// iterate over the sigs and their fields in <sol>
			// to find field <fieldname> in sig <signame>,
			// create a map that represents the tuples in the
			// corresponding relation, return the map
			// hint: use methods A4Solution.getAllReachableSigs() and
			// Sig.getFields() to iterate over all sigs and fields in <sol>;
			// use method A4Solution.eval(f) to get the value of field f in <sol>;
			// use method A4Tuple.atom(i) to get atom at position i in the tuple
			
			// your code goes here
		
		Map<String, String> ret = new HashMap<String, String>();
		SafeList<Sig> sigs = sol.getAllReachableSigs();
		for (Sig s : sigs) {
			//System.out.println(s.label);
			if (s.toString().equals("this/"+signame)) {
				SafeList<Field> fields = s.getFields();
				for (Field f : fields) {
					//System.out.println(f.toString());
					fieldname = "field (this/"+signame+" <: "+fieldname+")";
					if (f.toString().equals(fieldname)) {
						A4TupleSet a4_set = sol.eval(f);
						//System.out.println(a4_set.size());
						for (A4Tuple tuple : a4_set) {
							ret.put(tuple.atom(0), tuple.atom(1));
							//System.out.println(tuple.atom(0) + ", " + tuple.atom(1));
						}
					}
				}
			}
		}
		return ret;
	}
		
	private static String createProgram(A4Solution sol,
			Map<String, String> supertype,
			Map<String, String> implementS) {
			// assume input map <supertype> is already initialized
			// to represent the value of "ext" relation in <sol>
			// assume input map <implementS> is already initialized
			// to represent the value of "impl" relation in <sol>
			// return the Java program represented by <sol>
			
			// your code goes here
		
		String result = "";
		SafeList<Sig> sigs = sol.getAllReachableSigs();
		for (Sig s : sigs) {
			A4TupleSet a4_set = sol.eval(s);
			for (A4Tuple a : a4_set) {
				String atom = a.atom(0);
				if (!atom.contains("Object")) {
					String relation = supertype.get(atom);
					String impl_relation = implementS.get(atom);
					atom = Character.toString(atom.charAt(atom.length()-1));
					if (s.label.equals("this/Concrete")) {
						result += "class C" + atom;
						String relation_num = Character.toString(relation.charAt(relation.length()-1));
						if (relation.contains("Concrete")) {
							result += " extends C" + relation_num;
						} else if (relation.contains("Abstract")) {
							result += " extends A" + relation_num;
						}
						if (impl_relation != null) {
							String impl_relation_num = Character.toString(impl_relation.charAt(impl_relation.length()-1));
							result += " implements I" + impl_relation_num;
						}
						result += " {}\n";
						
					} else if (s.label.equals("this/Abstract")) {
						result += "abstract class A" + atom;
						String relation_num = Character.toString(relation.charAt(relation.length()-1));
						if (relation.contains("Concrete")) {
							result += " extends C" + relation_num;
						} else if (relation.contains("Abstract")) {
							result += " extends A" + relation_num;
						}
						if (impl_relation != null) {
							String impl_relation_num = Character.toString(impl_relation.charAt(impl_relation.length()-1));
							result += " implements I" + impl_relation_num;
						}
						result += " {}\n";
						
 					} else if (s.label.equals("this/Interface")) {
						result += "interface I" + atom;
						if (relation != null) {
							String relation_num = Character.toString(relation.charAt(relation.length()-1));
							result += " extends I" + relation_num;
						}
						result += " {}\n";
					}
				}
			}
		} 
		return result;
	}
}