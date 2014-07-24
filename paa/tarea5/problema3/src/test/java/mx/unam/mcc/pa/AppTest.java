package mx.unam.mcc.pa;

import junit.framework.Test;
import junit.framework.TestCase;
import junit.framework.TestSuite;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import org.apache.commons.beanutils.BeanPredicate;
import org.apache.commons.collections.CollectionUtils;
import org.apache.commons.collections.functors.EqualPredicate;

/**
 * Unit test for simple App.
 */
public class AppTest 
    extends TestCase
{
    /**
     * Create the test case
     *
     * @param testName name of the test case
     */
    public AppTest( String testName )
    {
        super( testName );
    }

    /**
     * @return the suite of tests being tested
     */
    public static Test suite()
    {
        return new TestSuite( AppTest.class );
    }

    /**
     * Rigourous Test :-)
     */
    public void testApp()
    {
        List<Person> personList = new ArrayList<Person>();
        personList.add(new Person("ganesh", "gowtham", 25000));
        personList.add(new Person("britney", "spears", 45000));
        personList.add(new Person("ganesh", "tom", 35000));
        personList.add(new Person("sunny", "dummy", 45000));

        String propertyName="firstName";
        String value="ganesh";

        EqualPredicate nameEqlPredicate = new EqualPredicate(value);
        BeanPredicate beanPredicate = new BeanPredicate(propertyName, nameEqlPredicate);
        Collection<Person> filteredCollection = CollectionUtils.select(personList, beanPredicate);
        System.out.println("Below are person object(s) whose " + propertyName + " is " + value);
        System.out.println("Matches for entered criteria "
                           + CollectionUtils.countMatches(personList, beanPredicate));
        for (Person person : filteredCollection) {
            System.out.println(person);
        }

        assertTrue( true );
    }


}
