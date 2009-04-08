package org.jmlspecs.jml4.fspv.theory.ast;

import org.eclipse.jdt.internal.compiler.ast.ASTNode;
import org.eclipse.jdt.internal.compiler.ast.TrueLiteral;

public class TheoryBooleanLiteral extends TheoryLiteral {

	public TheoryBooleanLiteral(ASTNode base, Theory theory) {
		super(base, theory);
		// TODO Auto-generated constructor stub
	}

	public static TheoryBooleanLiteral makeTrue(Theory theory) {
		return new TheoryBooleanLiteral(new TrueLiteral(0,0), theory);
	}

	public boolean isTrue() {
		return (this.base instanceof TrueLiteral);
	}
	
	public void traverse(TheoryVisitor visitor) {
		visitor.visit(this);
		visitor.endVisit(this);
	}


}


/*
No from me.  Here's the reason(s):

1) You should never drop guild and start helping Tindra (Guardian) to kill your fellow Acolytes just because she is in a group powerleveling you!  I relactuntly mediated and I took our guys from DMC to East ruins and help them level with my Demo.  I pleaded with him (Guuts--Cume's alt) to drop the Guardian group and come with us, he refused persistently!  
2) He told me that he has a "personal alliance" with LiF--not sure what the status is ATM.
3) He told me that he is in the Acolytes because he wants to PVE and we do it the best.  So what if we stop PVEing or we are no longer that good?

Now to Cyme's benefit he:
1) helped me with my Demo spec and helped demonstrated some strategies.
2) is an awesome PVPer!  I believe the best demo in the server, so when you are that good some ego is warranted :D :D
3) is active!

So all in all if not for him quiting the guild to kill those two Acolytes my vote you have been a Yes!

Theo...
*/