//  /*--------------------------------------------------------*\
//  |   Main Program: Glossary using HTML
//  |*--------------------------------------------------------*|
//  |   Date:   4/16/2012      
//  |   Author:   Brett Koenig    
//  |   
//  |   Brief User's Manual:
//  |   Taking an input file, marks it up with
//  |   HTML tags to display the contents in a 
//  |   Glossary, alphabetically with links to
//  |   terms in the definitions.  
//  |   
//  \*--------------------------------------------------------*/

#include "RESOLVE_Foundation.h"

#include "CT/Set/Kernel_1_C.h"

#include "CT/Partial_Map/Kernel_1_C.h"

#include "CT/Sorting_Machine/Kernel_1_C.h"

#include "CI/Text/Are_In_Order_1.h"

#include "CT/Queue/Kernel_1a_C.h"

//Concrete instances

concrete_instance
class Partial_Map :
    instantiates Partial_Map_Kernel_1_C <Text, Text>
{};

concrete_instance
class Set_Of_Text :
    instantiates Set_Kernel_1_C <Text>
{};

concrete_instance
class Set_Of_Character :
    instantiates Set_Kernel_1_C <Character>
{};

concrete_instance
class Sorting_Machine_Of_Text :
    instantiates Sorting_Machine_Kernel_1_C <Text, Text_Are_In_Order_1>
{};

concrete_instance
class Queue_Of_Text :
    instantiates Queue_Kernel_1a_C <Text>
{};


//----------------------------------------------------------------------
//----------------------------------------------------------------------

//global procedure bodies

global_procedure_body Create_Separators_Set (
    produces Set_Of_Character& separators
    )
{
    object catalyst Character c;

    separators.Clear ();

    c = ' ';
    separators.Add (c);
    c = '\t';
    separators.Add (c);
    c = '\n';
    separators.Add (c);
    c = '.';
    separators.Add (c);
    c = ',';
    separators.Add (c);
    c = ';';
    separators.Add (c);
    c = ':';
    separators.Add (c);
    c = '(';
    separators.Add (c);
    c = ')';   
    separators.Add (c);
    c = '[';
    separators.Add (c);
    c = ']';
    separators.Add (c);
    c = '{';
    separators.Add (c);
    c = '}';
    separators.Add (c);
    c = '<';
    separators.Add (c);
    c = '>';
    separators.Add (c);
}

//----------------------------------------------------------------------

global_procedure_body Remove_First_Word (
        alters Text& t,
    alters Set_Of_Character& separators,
        produces Text& leading_separators,
        produces Text& word
    )
{
    assert (t.Length () > 0,
        "there exists c: character\n"
        "    (<c> is suffix of t)");
    assert (separators.Is_Member (t[t.Length () - 1]),
        "there exists c: character\n"
        "    (<c> is suffix of t  and\n"
        "     c is in SEPARATORS)");
       
    object Character sentinel = 'X';
    
    leading_separators.Clear ();
    word.Clear ();

    // Add a sentinel non-separators character to the end of t
    
    t.Add (t.Length (), sentinel);

    // Remove leading separators characters from t; loop can't run
    // off the end of t because of the sentinel
    
    while (separators.Is_Member (t[0]))
    {
        object Character ch;
    t.Remove (0, ch);
    leading_separators.Add (leading_separators.Length (), ch);
    }

    // Remove the word now at the start of t, if any
    
    if (t.Length () > 1)
    {
    // There was a word in #t, so remove the longest prefix of t
    // that is a word, AND the sentinel

    while (not separators.Is_Member (t[0]))
    {
        object Character ch;
        t.Remove (0, ch);
        word.Add (word.Length (), ch);
    }

    t.Remove (t.Length () - 1, sentinel);
    }
    else
    {
    // There were no words in #t, so remove the sentinel (the only
    // character left in t) and return, since leading_separators
    // and word have correct values now

    t.Remove (0, sentinel);
    }    
}

//----------------------------------------------------------------------


//takes a word passed to it and outputs in Red Bold in HTML
global_procedure_body Put_To_Entry(
    alters Character_OStream& output,
    preserves Text word
    )
{
    output << "<P><A NAME=\"" << word << "\"></A><FONT COLOR=RED>";
    output << "<B><I>" << word << "</I></B></FONT></P> \n \n";
}

//----------------------------------------------------------------------


//takes a word passed to it and outputs a link
global_procedure_body Put_To_Link(
    alters Character_OStream& output,
    preserves Text word
    )
{
    output << "<A HREF=\"#" << word << "\">" << word << "</A>";
}

//----------------------------------------------------------------------

//concatenates the second part of the definition onto the
//end of the exisitng part of the definition 
global_procedure_body Concatenate(
    alters Text& def,
    consumes Text& line
    )
{
    object Character c;
    
    while(line.Length() > 0)
    {
    line.Remove(0,c);
    def.Add(def.Length(), c);
    }
}

//----------------------------------------------------------------------

//creates a sorted partial map containing glossary entries as
//the d-item and their definitions as the r-item.
//also creates a set object containing only glossary entries
global_procedure_body Get_Entries(
    alters Character_IStream& input,
    produces Set_Of_Text& entries,
    produces Partial_Map& map
    )
{
    object Set_Of_Character separators;

    Create_Separators_Set(separators);
    
    object Text line, ls, word, word_copy,word_copy2, def, a;
    object Boolean is_keyword = true;

    while(!input.At_EOS())
    {
    input >> line;
    line.Add(line.Length(), '\n');
    if(line.Length() > 1)
    {     
        if(is_keyword)
        {
        Remove_First_Word(line, separators, ls, word);
        word_copy = word;
        word_copy2 = word;
        entries.Add(word_copy);
        map.Define(word_copy2, a);
        is_keyword = false;
        }
        else if(map.Is_Defined(word))
        {
        map.Undefine(word, word_copy2, def);
        Concatenate(def, line);
        map.Define(word_copy2, def);
        }
    }
    else
    {
        is_keyword = true;
    }
    
    }
}
    

//----------------------------------------------------------------------

//creates the index at the top of the web page
global_procedure_body Index(
    alters Queue_Of_Text& keywords,
    alters Character_OStream& output
    )
{
    object Text word;
    object Integer i;
    
    while(i < keywords.Length())
    {
    keywords.Dequeue(word);
    output << "<LI><A HREF=\"#" << word << "\">" << word << "</A></LI> \n";
    keywords.Enqueue(word);
    i = i+1;
    }
}

//----------------------------------------------------------------------
//----------------------------------------------------------------------

program_body main()
{
    object Character_IStream input;
    object Character_OStream output;
    object Set_Of_Text entries;
    object Sorting_Machine_Of_Text sorter;
    object Queue_Of_Text keywords;
    object Set_Of_Character separators;

    Create_Separators_Set(separators);
    
    input.Open_External("");
    output.Open_External("");

    object Partial_Map EWD; //entries with definitons
    Get_Entries(input, entries, EWD);
    
    output << "<HTML> \n" << "<HEAD> \n" << "<TITLE>Glossary</TITLE> \n";
    output << "</HEAD> \n" << "<BODY BGCOLOR=WHITE> \n" << "<Font SIZE=+2> \n";

    object Text word;
    
    while(entries.Size()>0)
    {
    entries.Remove_Any(word);
    sorter.Insert(word);   
    }
    sorter.Change_To_Extraction_Phase();
    while(sorter.Size()>0)
    {
    sorter.Remove_First(word);
    object Text copy = word;
    entries.Add(copy);
    keywords.Enqueue(word);
    }
    
    output << "\n <H3>Index</H3> \n" << "\n <UL> \n";
    Index(keywords, output);
    output << "</UL> \n <HR> \n";

    object Text d_item, r_item, def_word;
    object Text ls;

    output << "<H3>Terms and Definitions</H3> \n";
    while(keywords.Length() > 0)
    {
    keywords.Dequeue(word);
    EWD.Undefine(word, d_item, r_item);
    Put_To_Entry(output, d_item);
    output << "<UL> \n" << "<P>";
    while(r_item.Length() > 0)
    {
        Remove_First_Word(r_item, separators, ls, def_word);
        if(entries.Is_Member(def_word))
        {
        output << ls;
        Put_To_Link(output, def_word);           
        }
        else
        {
        output << ls << def_word;
        }
    }
    output << "</P> \n" << "</UL> \n \n";
    }

    output << "<HR> \n \n </Font> \n </BODY> \n </HTML>";

    input.Close_External();
    output.Close_External();
}