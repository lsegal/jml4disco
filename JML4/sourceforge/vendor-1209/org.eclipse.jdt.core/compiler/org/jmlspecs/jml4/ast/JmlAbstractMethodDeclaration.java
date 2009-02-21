
package org.jmlspecs.jml4.ast;

import org.jmlspecs.jml4.esc.result.lang.Result;

public interface JmlAbstractMethodDeclaration {

	void initJmlModifiersFromAnnotations();
	JmlMethodSpecification getSpecification();
	void setEscResults(Result[] results);
	
}
