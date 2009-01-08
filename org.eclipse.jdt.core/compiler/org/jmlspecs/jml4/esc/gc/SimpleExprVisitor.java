package org.jmlspecs.jml4.esc.gc;

import org.jmlspecs.jml4.esc.gc.lang.simple.SimpleAssignment;
import org.jmlspecs.jml4.esc.gc.lang.simple.expr.SimpleArrayAllocationExpression;
import org.jmlspecs.jml4.esc.gc.lang.simple.expr.SimpleArrayReference;
import org.jmlspecs.jml4.esc.gc.lang.simple.expr.SimpleBinaryExpression;
import org.jmlspecs.jml4.esc.gc.lang.simple.expr.SimpleBooleanConstant;
import org.jmlspecs.jml4.esc.gc.lang.simple.expr.SimpleConditionalExpression;
import org.jmlspecs.jml4.esc.gc.lang.simple.expr.SimpleExpression;
import org.jmlspecs.jml4.esc.gc.lang.simple.expr.SimpleFieldReference;
import org.jmlspecs.jml4.esc.gc.lang.simple.expr.SimpleIntegerConstant;
import org.jmlspecs.jml4.esc.gc.lang.simple.expr.SimpleMessageSend;
import org.jmlspecs.jml4.esc.gc.lang.simple.expr.SimpleNotExpression;
import org.jmlspecs.jml4.esc.gc.lang.simple.expr.SimpleOldExpression;
import org.jmlspecs.jml4.esc.gc.lang.simple.expr.SimplePostfixExpression;
import org.jmlspecs.jml4.esc.gc.lang.simple.expr.SimpleQuantifiedExpression;
import org.jmlspecs.jml4.esc.gc.lang.simple.expr.SimpleThisReference;
import org.jmlspecs.jml4.esc.gc.lang.simple.expr.SimpleVariable;

public interface SimpleExprVisitor {
	
	SimpleExpression visit(SimpleAssignment expr);  
	SimpleExpression visit(SimpleBinaryExpression expr);  
	SimpleExpression visit(SimpleBooleanConstant expr);  
	SimpleExpression visit(SimpleConditionalExpression expr);  
	SimpleExpression visit(SimpleIntegerConstant expr);  
	SimpleExpression visit(SimpleMessageSend expr);  
	SimpleExpression visit(SimpleOldExpression expr);  
	SimpleExpression visit(SimplePostfixExpression expr);  
	SimpleExpression visit(SimpleQuantifiedExpression expr);  
	SimpleExpression visit(SimpleNotExpression expr);  
	SimpleExpression visit(SimpleVariable expr);  
	SimpleExpression visit(SimpleFieldReference expr);
	SimpleExpression visit(SimpleSuperReference superRef);  
	SimpleExpression visit(SimpleThisReference thisRef);
	SimpleExpression visit(SimpleArrayReference arrayRef);
	SimpleExpression visit(SimpleArrayAllocationExpression arrayAlloc);  

}
