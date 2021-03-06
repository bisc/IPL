/*
 * generated by Xtext 2.10.0
 */
package org.xtext.example.ipl.tests

import com.google.inject.Inject
import org.eclipse.xtext.testing.InjectWith
import org.eclipse.xtext.testing.XtextRunner
import org.eclipse.xtext.testing.util.ParseHelper
import org.junit.Assert
import org.junit.Test
import org.junit.runner.RunWith
import org.xtext.example.ipl.iPL.IPLSpec

@RunWith(XtextRunner)
@InjectWith(IPLInjectorProvider)
class IPLParsingTestSpec{

	@Inject
	ParseHelper<IPLSpec> specParseHelper
	
	@Test 
	def void loadSpecs() {
		val result = specParseHelper.parse('''
			Hello Xtext!
		''')
		//Assert.assertNull(result.decls)
		Assert.assertTrue(result.decls.empty)
	}

}
