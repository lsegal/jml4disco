package org.jmlspecs.jml4.esc.gc;

import org.jmlspecs.jml4.esc.gc.lang.sugared.SugaredAssert;
import org.jmlspecs.jml4.esc.gc.lang.sugared.SugaredAssume;
import org.jmlspecs.jml4.esc.gc.lang.sugared.SugaredBreakStatement;
import org.jmlspecs.jml4.esc.gc.lang.sugared.SugaredContinueStatement;
import org.jmlspecs.jml4.esc.gc.lang.sugared.SugaredExprStatement;
import org.jmlspecs.jml4.esc.gc.lang.sugared.SugaredGoto;
import org.jmlspecs.jml4.esc.gc.lang.sugared.SugaredHavoc;
import org.jmlspecs.jml4.esc.gc.lang.sugared.SugaredPostcondition;
import org.jmlspecs.jml4.esc.gc.lang.sugared.SugaredPrecondition;
import org.jmlspecs.jml4.esc.gc.lang.sugared.SugaredReturnStatement;
import org.jmlspecs.jml4.esc.gc.lang.sugared.SugaredSequence;
import org.jmlspecs.jml4.esc.gc.lang.sugared.SugaredStatement;
import org.jmlspecs.jml4.esc.gc.lang.sugared.SugaredVarDecl;
import org.jmlspecs.jml4.esc.gc.lang.sugared.SugaredWhileStatement;

public interface SugaredStatementVisitor {
	SugaredStatement visit(SugaredAssert stmt, SugaredStatement rest);
	SugaredStatement visit(SugaredAssume stmt, SugaredStatement rest);
	SugaredStatement visit(SugaredBreakStatement stmt, SugaredStatement rest);
	SugaredStatement visit(SugaredContinueStatement stmt, SugaredStatement rest);
	SugaredStatement visit(SugaredExprStatement stmt, SugaredStatement rest);
	SugaredStatement visit(SugaredHavoc stmt, SugaredStatement rest);
	SugaredStatement visit(SugaredGoto stmt, SugaredStatement rest);
	SugaredStatement visit(SugaredPostcondition stmt, SugaredStatement rest);
	SugaredStatement visit(SugaredPrecondition stmt, SugaredStatement rest);
	SugaredStatement visit(SugaredReturnStatement stmt, SugaredStatement rest);
	SugaredStatement visit(SugaredSequence stmt, SugaredStatement rest);
	SugaredStatement visit(SugaredVarDecl stmt, SugaredStatement rest);
	SugaredStatement visit(SugaredWhileStatement stmt, SugaredStatement rest);
}
