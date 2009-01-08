package org.jmlspecs.jml4.esc.gc;

import org.jmlspecs.jml4.esc.gc.lang.sugared.SugaredAssert;
import org.jmlspecs.jml4.esc.gc.lang.sugared.SugaredAssume;
import org.jmlspecs.jml4.esc.gc.lang.sugared.SugaredBlock;
import org.jmlspecs.jml4.esc.gc.lang.sugared.SugaredBreakStatement;
import org.jmlspecs.jml4.esc.gc.lang.sugared.SugaredContinueStatement;
import org.jmlspecs.jml4.esc.gc.lang.sugared.SugaredExprStatement;
import org.jmlspecs.jml4.esc.gc.lang.sugared.SugaredGoto;
import org.jmlspecs.jml4.esc.gc.lang.sugared.SugaredHavoc;
import org.jmlspecs.jml4.esc.gc.lang.sugared.SugaredIfStatement;
import org.jmlspecs.jml4.esc.gc.lang.sugared.SugaredPostcondition;
import org.jmlspecs.jml4.esc.gc.lang.sugared.SugaredPrecondition;
import org.jmlspecs.jml4.esc.gc.lang.sugared.SugaredProgram;
import org.jmlspecs.jml4.esc.gc.lang.sugared.SugaredReturnStatement;
import org.jmlspecs.jml4.esc.gc.lang.sugared.SugaredSequence;
import org.jmlspecs.jml4.esc.gc.lang.sugared.SugaredStatement;
import org.jmlspecs.jml4.esc.gc.lang.sugared.SugaredVarDecl;
import org.jmlspecs.jml4.esc.gc.lang.sugared.SugaredWhileStatement;

public interface SimplifyingVisitor {

	SugaredProgram visit(SugaredProgram sugaredProgram);
	SugaredBlock[] visit(SugaredBlock sugaredBlock);
	SugaredStatement visit(SugaredSequence sugaredSequence);
	SugaredStatement visit(SugaredAssert sugaredAssert);
	SugaredStatement visit(SugaredAssume sugaredAssume);
	SugaredStatement visit(SugaredIfStatement sugaredIfStatement);
	SugaredStatement visit(SugaredWhileStatement sugaredWhileStatement);
	SugaredStatement visit(SugaredVarDecl sugaredVarDecl);
	SugaredStatement visit(SugaredGoto sugaredGoto);
	SugaredStatement visit(SugaredBreakStatement sugaredBreakStatement);
	SugaredStatement visit(SugaredContinueStatement sugaredContinueStatement);
	SugaredStatement visit(SugaredExprStatement sugaredExprStatement);
	SugaredStatement visit(SugaredHavoc sugaredHavoc);
	SugaredStatement visit(SugaredReturnStatement sugaredReturn);
	SugaredStatement visit(SugaredPrecondition sugaredPrecondition);
	SugaredStatement visit(SugaredPostcondition sugaredPostcondition);
}
