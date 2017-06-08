/*
 * generated by Xtext 2.10.0
 */
package org.xtext.example.ipl.ui.outline

import org.eclipse.xtext.ui.editor.outline.impl.DefaultOutlineTreeProvider
import org.xtext.example.ipl.iPL.Fun

/**
 * Customization of the default outline structure.
 *
 * See https://www.eclipse.org/Xtext/documentation/304_ide_concepts.html#outline
 */
class IPLOutlineTreeProvider extends DefaultOutlineTreeProvider {
	def _text(Fun f) {
		System::out.println(f.name)
		f.name.name.toString
	}
}
