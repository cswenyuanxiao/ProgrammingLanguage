// Generated from Diggleby.g4 by ANTLR 4.9.1

package antlr;

import org.antlr.v4.runtime.Lexer;
import org.antlr.v4.runtime.CharStream;
import org.antlr.v4.runtime.Token;
import org.antlr.v4.runtime.TokenStream;
import org.antlr.v4.runtime.*;
import org.antlr.v4.runtime.atn.*;
import org.antlr.v4.runtime.dfa.DFA;
import org.antlr.v4.runtime.misc.*;

@SuppressWarnings({"all", "warnings", "unchecked", "unused", "cast"})
public class DigglebyLexer extends Lexer {
	static { RuntimeMetaData.checkVersion("4.9.1", RuntimeMetaData.VERSION); }

	protected static final DFA[] _decisionToDFA;
	protected static final PredictionContextCache _sharedContextCache =
		new PredictionContextCache();
	public static final int
		T__0=1, T__1=2, T__2=3, T__3=4, WS=5, COMMA=6, DEF=7, TRUE=8, FALSE=9, 
		INT=10, LET=11, IN=12, PLUS=13, MINUS=14, MUL=15, DIV=16, MOD=17, GT=18, 
		LT=19, EQQ=20, EQ=21, AND=22, OR=23, XOR=24, NOT=25, CONCAT=26, IF=27, 
		THEN=28, ELSE=29, PRINT=30, GETINPUT=31, COLON=32, LPAREN=33, RPAREN=34, 
		LBRACE=35, RBRACE=36, STR=37, IDENT=38;
	public static String[] channelNames = {
		"DEFAULT_TOKEN_CHANNEL", "HIDDEN"
	};

	public static String[] modeNames = {
		"DEFAULT_MODE"
	};

	private static String[] makeRuleNames() {
		return new String[] {
			"T__0", "T__1", "T__2", "T__3", "WS", "COMMA", "DEF", "TRUE", "FALSE", 
			"INT", "LET", "IN", "PLUS", "MINUS", "MUL", "DIV", "MOD", "GT", "LT", 
			"EQQ", "EQ", "AND", "OR", "XOR", "NOT", "CONCAT", "IF", "THEN", "ELSE", 
			"PRINT", "GETINPUT", "COLON", "LPAREN", "RPAREN", "LBRACE", "RBRACE", 
			"STR", "IDENT"
		};
	}
	public static final String[] ruleNames = makeRuleNames();

	private static String[] makeLiteralNames() {
		return new String[] {
			null, "'Bool'", "'Int'", "'String'", "'Unit'", null, "','", "'def'", 
			"'true'", "'false'", null, "'let'", "'in'", "'+'", "'-'", "'*'", "'/'", 
			"'%'", "'>'", "'<'", "'=='", "'='", "'&&'", "'||'", "'^'", "'!'", "'concat'", 
			"'if'", "'then'", "'else'", "'print'", "'getInput'", "':'", "'('", "')'", 
			"'{'", "'}'"
		};
	}
	private static final String[] _LITERAL_NAMES = makeLiteralNames();
	private static String[] makeSymbolicNames() {
		return new String[] {
			null, null, null, null, null, "WS", "COMMA", "DEF", "TRUE", "FALSE", 
			"INT", "LET", "IN", "PLUS", "MINUS", "MUL", "DIV", "MOD", "GT", "LT", 
			"EQQ", "EQ", "AND", "OR", "XOR", "NOT", "CONCAT", "IF", "THEN", "ELSE", 
			"PRINT", "GETINPUT", "COLON", "LPAREN", "RPAREN", "LBRACE", "RBRACE", 
			"STR", "IDENT"
		};
	}
	private static final String[] _SYMBOLIC_NAMES = makeSymbolicNames();
	public static final Vocabulary VOCABULARY = new VocabularyImpl(_LITERAL_NAMES, _SYMBOLIC_NAMES);

	/**
	 * @deprecated Use {@link #VOCABULARY} instead.
	 */
	@Deprecated
	public static final String[] tokenNames;
	static {
		tokenNames = new String[_SYMBOLIC_NAMES.length];
		for (int i = 0; i < tokenNames.length; i++) {
			tokenNames[i] = VOCABULARY.getLiteralName(i);
			if (tokenNames[i] == null) {
				tokenNames[i] = VOCABULARY.getSymbolicName(i);
			}

			if (tokenNames[i] == null) {
				tokenNames[i] = "<INVALID>";
			}
		}
	}

	@Override
	@Deprecated
	public String[] getTokenNames() {
		return tokenNames;
	}

	@Override

	public Vocabulary getVocabulary() {
		return VOCABULARY;
	}


	public DigglebyLexer(CharStream input) {
		super(input);
		_interp = new LexerATNSimulator(this,_ATN,_decisionToDFA,_sharedContextCache);
	}

	@Override
	public String getGrammarFileName() { return "Diggleby.g4"; }

	@Override
	public String[] getRuleNames() { return ruleNames; }

	@Override
	public String getSerializedATN() { return _serializedATN; }

	@Override
	public String[] getChannelNames() { return channelNames; }

	@Override
	public String[] getModeNames() { return modeNames; }

	@Override
	public ATN getATN() { return _ATN; }

	public static final String _serializedATN =
		"\3\u608b\ua72a\u8133\ub9ed\u417c\u3be7\u7786\u5964\2(\u00e2\b\1\4\2\t"+
		"\2\4\3\t\3\4\4\t\4\4\5\t\5\4\6\t\6\4\7\t\7\4\b\t\b\4\t\t\t\4\n\t\n\4\13"+
		"\t\13\4\f\t\f\4\r\t\r\4\16\t\16\4\17\t\17\4\20\t\20\4\21\t\21\4\22\t\22"+
		"\4\23\t\23\4\24\t\24\4\25\t\25\4\26\t\26\4\27\t\27\4\30\t\30\4\31\t\31"+
		"\4\32\t\32\4\33\t\33\4\34\t\34\4\35\t\35\4\36\t\36\4\37\t\37\4 \t \4!"+
		"\t!\4\"\t\"\4#\t#\4$\t$\4%\t%\4&\t&\4\'\t\'\3\2\3\2\3\2\3\2\3\2\3\3\3"+
		"\3\3\3\3\3\3\4\3\4\3\4\3\4\3\4\3\4\3\4\3\5\3\5\3\5\3\5\3\5\3\6\6\6f\n"+
		"\6\r\6\16\6g\3\6\3\6\3\7\3\7\3\b\3\b\3\b\3\b\3\t\3\t\3\t\3\t\3\t\3\n\3"+
		"\n\3\n\3\n\3\n\3\n\3\13\6\13~\n\13\r\13\16\13\177\3\f\3\f\3\f\3\f\3\r"+
		"\3\r\3\r\3\16\3\16\3\17\3\17\3\20\3\20\3\21\3\21\3\22\3\22\3\23\3\23\3"+
		"\24\3\24\3\25\3\25\3\25\3\26\3\26\3\27\3\27\3\27\3\30\3\30\3\30\3\31\3"+
		"\31\3\32\3\32\3\33\3\33\3\33\3\33\3\33\3\33\3\33\3\34\3\34\3\34\3\35\3"+
		"\35\3\35\3\35\3\35\3\36\3\36\3\36\3\36\3\36\3\37\3\37\3\37\3\37\3\37\3"+
		"\37\3 \3 \3 \3 \3 \3 \3 \3 \3 \3!\3!\3\"\3\"\3#\3#\3$\3$\3%\3%\3&\3&\7"+
		"&\u00d5\n&\f&\16&\u00d8\13&\3&\3&\3\'\3\'\7\'\u00de\n\'\f\'\16\'\u00e1"+
		"\13\'\2\2(\3\3\5\4\7\5\t\6\13\7\r\b\17\t\21\n\23\13\25\f\27\r\31\16\33"+
		"\17\35\20\37\21!\22#\23%\24\'\25)\26+\27-\30/\31\61\32\63\33\65\34\67"+
		"\359\36;\37= ?!A\"C#E$G%I&K\'M(\3\2\6\5\2\13\f\17\17\"\"\3\2\62;\4\2C"+
		"\\c|\5\2\62;C\\c|\2\u00e5\2\3\3\2\2\2\2\5\3\2\2\2\2\7\3\2\2\2\2\t\3\2"+
		"\2\2\2\13\3\2\2\2\2\r\3\2\2\2\2\17\3\2\2\2\2\21\3\2\2\2\2\23\3\2\2\2\2"+
		"\25\3\2\2\2\2\27\3\2\2\2\2\31\3\2\2\2\2\33\3\2\2\2\2\35\3\2\2\2\2\37\3"+
		"\2\2\2\2!\3\2\2\2\2#\3\2\2\2\2%\3\2\2\2\2\'\3\2\2\2\2)\3\2\2\2\2+\3\2"+
		"\2\2\2-\3\2\2\2\2/\3\2\2\2\2\61\3\2\2\2\2\63\3\2\2\2\2\65\3\2\2\2\2\67"+
		"\3\2\2\2\29\3\2\2\2\2;\3\2\2\2\2=\3\2\2\2\2?\3\2\2\2\2A\3\2\2\2\2C\3\2"+
		"\2\2\2E\3\2\2\2\2G\3\2\2\2\2I\3\2\2\2\2K\3\2\2\2\2M\3\2\2\2\3O\3\2\2\2"+
		"\5T\3\2\2\2\7X\3\2\2\2\t_\3\2\2\2\13e\3\2\2\2\rk\3\2\2\2\17m\3\2\2\2\21"+
		"q\3\2\2\2\23v\3\2\2\2\25}\3\2\2\2\27\u0081\3\2\2\2\31\u0085\3\2\2\2\33"+
		"\u0088\3\2\2\2\35\u008a\3\2\2\2\37\u008c\3\2\2\2!\u008e\3\2\2\2#\u0090"+
		"\3\2\2\2%\u0092\3\2\2\2\'\u0094\3\2\2\2)\u0096\3\2\2\2+\u0099\3\2\2\2"+
		"-\u009b\3\2\2\2/\u009e\3\2\2\2\61\u00a1\3\2\2\2\63\u00a3\3\2\2\2\65\u00a5"+
		"\3\2\2\2\67\u00ac\3\2\2\29\u00af\3\2\2\2;\u00b4\3\2\2\2=\u00b9\3\2\2\2"+
		"?\u00bf\3\2\2\2A\u00c8\3\2\2\2C\u00ca\3\2\2\2E\u00cc\3\2\2\2G\u00ce\3"+
		"\2\2\2I\u00d0\3\2\2\2K\u00d2\3\2\2\2M\u00db\3\2\2\2OP\7D\2\2PQ\7q\2\2"+
		"QR\7q\2\2RS\7n\2\2S\4\3\2\2\2TU\7K\2\2UV\7p\2\2VW\7v\2\2W\6\3\2\2\2XY"+
		"\7U\2\2YZ\7v\2\2Z[\7t\2\2[\\\7k\2\2\\]\7p\2\2]^\7i\2\2^\b\3\2\2\2_`\7"+
		"W\2\2`a\7p\2\2ab\7k\2\2bc\7v\2\2c\n\3\2\2\2df\t\2\2\2ed\3\2\2\2fg\3\2"+
		"\2\2ge\3\2\2\2gh\3\2\2\2hi\3\2\2\2ij\b\6\2\2j\f\3\2\2\2kl\7.\2\2l\16\3"+
		"\2\2\2mn\7f\2\2no\7g\2\2op\7h\2\2p\20\3\2\2\2qr\7v\2\2rs\7t\2\2st\7w\2"+
		"\2tu\7g\2\2u\22\3\2\2\2vw\7h\2\2wx\7c\2\2xy\7n\2\2yz\7u\2\2z{\7g\2\2{"+
		"\24\3\2\2\2|~\t\3\2\2}|\3\2\2\2~\177\3\2\2\2\177}\3\2\2\2\177\u0080\3"+
		"\2\2\2\u0080\26\3\2\2\2\u0081\u0082\7n\2\2\u0082\u0083\7g\2\2\u0083\u0084"+
		"\7v\2\2\u0084\30\3\2\2\2\u0085\u0086\7k\2\2\u0086\u0087\7p\2\2\u0087\32"+
		"\3\2\2\2\u0088\u0089\7-\2\2\u0089\34\3\2\2\2\u008a\u008b\7/\2\2\u008b"+
		"\36\3\2\2\2\u008c\u008d\7,\2\2\u008d \3\2\2\2\u008e\u008f\7\61\2\2\u008f"+
		"\"\3\2\2\2\u0090\u0091\7\'\2\2\u0091$\3\2\2\2\u0092\u0093\7@\2\2\u0093"+
		"&\3\2\2\2\u0094\u0095\7>\2\2\u0095(\3\2\2\2\u0096\u0097\7?\2\2\u0097\u0098"+
		"\7?\2\2\u0098*\3\2\2\2\u0099\u009a\7?\2\2\u009a,\3\2\2\2\u009b\u009c\7"+
		"(\2\2\u009c\u009d\7(\2\2\u009d.\3\2\2\2\u009e\u009f\7~\2\2\u009f\u00a0"+
		"\7~\2\2\u00a0\60\3\2\2\2\u00a1\u00a2\7`\2\2\u00a2\62\3\2\2\2\u00a3\u00a4"+
		"\7#\2\2\u00a4\64\3\2\2\2\u00a5\u00a6\7e\2\2\u00a6\u00a7\7q\2\2\u00a7\u00a8"+
		"\7p\2\2\u00a8\u00a9\7e\2\2\u00a9\u00aa\7c\2\2\u00aa\u00ab\7v\2\2\u00ab"+
		"\66\3\2\2\2\u00ac\u00ad\7k\2\2\u00ad\u00ae\7h\2\2\u00ae8\3\2\2\2\u00af"+
		"\u00b0\7v\2\2\u00b0\u00b1\7j\2\2\u00b1\u00b2\7g\2\2\u00b2\u00b3\7p\2\2"+
		"\u00b3:\3\2\2\2\u00b4\u00b5\7g\2\2\u00b5\u00b6\7n\2\2\u00b6\u00b7\7u\2"+
		"\2\u00b7\u00b8\7g\2\2\u00b8<\3\2\2\2\u00b9\u00ba\7r\2\2\u00ba\u00bb\7"+
		"t\2\2\u00bb\u00bc\7k\2\2\u00bc\u00bd\7p\2\2\u00bd\u00be\7v\2\2\u00be>"+
		"\3\2\2\2\u00bf\u00c0\7i\2\2\u00c0\u00c1\7g\2\2\u00c1\u00c2\7v\2\2\u00c2"+
		"\u00c3\7K\2\2\u00c3\u00c4\7p\2\2\u00c4\u00c5\7r\2\2\u00c5\u00c6\7w\2\2"+
		"\u00c6\u00c7\7v\2\2\u00c7@\3\2\2\2\u00c8\u00c9\7<\2\2\u00c9B\3\2\2\2\u00ca"+
		"\u00cb\7*\2\2\u00cbD\3\2\2\2\u00cc\u00cd\7+\2\2\u00cdF\3\2\2\2\u00ce\u00cf"+
		"\7}\2\2\u00cfH\3\2\2\2\u00d0\u00d1\7\177\2\2\u00d1J\3\2\2\2\u00d2\u00d6"+
		"\7$\2\2\u00d3\u00d5\t\4\2\2\u00d4\u00d3\3\2\2\2\u00d5\u00d8\3\2\2\2\u00d6"+
		"\u00d4\3\2\2\2\u00d6\u00d7\3\2\2\2\u00d7\u00d9\3\2\2\2\u00d8\u00d6\3\2"+
		"\2\2\u00d9\u00da\7$\2\2\u00daL\3\2\2\2\u00db\u00df\t\4\2\2\u00dc\u00de"+
		"\t\5\2\2\u00dd\u00dc\3\2\2\2\u00de\u00e1\3\2\2\2\u00df\u00dd\3\2\2\2\u00df"+
		"\u00e0\3\2\2\2\u00e0N\3\2\2\2\u00e1\u00df\3\2\2\2\7\2g\177\u00d6\u00df"+
		"\3\b\2\2";
	public static final ATN _ATN =
		new ATNDeserializer().deserialize(_serializedATN.toCharArray());
	static {
		_decisionToDFA = new DFA[_ATN.getNumberOfDecisions()];
		for (int i = 0; i < _ATN.getNumberOfDecisions(); i++) {
			_decisionToDFA[i] = new DFA(_ATN.getDecisionState(i), i);
		}
	}
}