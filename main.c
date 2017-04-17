//Implementierungen zu der Masterarbeit "Kombinatorische Algorithmen für LWE"
//Geschrieben an der Ruhr-Universität Bochum im Jahr 2017
//Autor: Jan-Christoph Luhmann

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <time.h>
#include <math.h>
#include <string.h>


#define PI 3.14159265358979323846

//Parameter des LWE-Problems
const uint32_t  q = 13;
const uint32_t  k = 10;

//Parameter der Normalverteilung
const uint32_t  sigma = 1;
const uint32_t  mu = 0;

//Berechne das Inverse eines Elements in F_q mit Hilfe des EEA
//Parameter: elem1 = das zu invertierende Element
uint32_t inverse(uint32_t elem1)
{
    uint32_t u,v,s,t,a,b,c,buf;
    u = 1;
    v = 0;
    s = 0;
    t = 1;

    a = elem1;
    b = q;

    while( b != 0)
    {
        c = ceil(a/b);

        buf = a;
        a = b;
        b = buf-c*b;

        buf = u;
        u = s;
        s = buf-c*s;

        buf = v;
        v = t;
        t = buf-c*t;
    }

    return (u+q)%q;
}

uint32_t lweOrakel(uint32_t error[],uint32_t s[], uint32_t* a)
{
    //Initaliziere Hilfsvariablen:
    uint32_t j,e,buffer;
    buffer = 0;

    //Ziehe zufällige a_i's und berechne das Innere Produkt <a*s> = b
    for(int i=0;i<k;i++)
    {
        a[i] = rand()%q;
        buffer = (buffer + ((a[i]*s[i]) % q)) % q;
    }

    //Addiere den Fehler
    j = rand() % 100;
    e = error[j];
    buffer = (buffer+e) % q;

    return buffer;
}

//Diese Funktion berechnet Test (Kombinatorische Algorithmen für LWE, ALgorithmus 3)
//Parameter: sbar[] = die Hypothese, die getestet werden soll, A[][],b[] = enthält die LWE-Samples
//                    m,c = die berechneten Parameter die Test brauch
uint32_t test(uint32_t sbar[], uint32_t A[][k], uint32_t b[], uint32_t m, uint32_t c)
{
    //Initaliziere Parameter und Hilfsvariablen:
    uint32_t check[m];
    uint32_t counter = 0;
    uint32_t bbuf[m];
    uint32_t Abuf[m][k];

    //Belege den Buffer:
    for(int i=0;i<m;i++)
    {
        for(int j=0;j<k;j++)
        {
            Abuf[i][j] = A[i][j];
        }
        bbuf[i] = b[i];
    }

    //Führe den eigentlichen Algorithmus durch
    for(int i=0;i<m;i++)
    {
        check[i] = 0;
        for(int j=0;j<k;j++)
        {
            Abuf[i][j] = (Abuf[i][j]*sbar[j]) % q;
            check[i] = (check[i] + Abuf[i][j]) % q;
        }
        bbuf[i] = (bbuf[i] - check[i]) % q;
    }

    for(int i=0;i<m;i++)
    {
        if(bbuf[i] == 0)
        {
            counter = counter + 1;
        }
    }

    if(counter >= c)
    {
        return 1;
    } else {
        return 0;
    }
}

//Diese Funktion führt die Gauß-Elimination aus gibt den gesuchten Vektor zurück
//(Ausgeschriebener Pseudocode, der entsprechenden WIkipedia-Seite):
//Parameter: matrix[][] = Matrix, die invertiert werden soll, vektor[] = b des Gleichungssystem Ax = b
//           Die Ausgabe wird in vektor gespeichert.
uint32_t gauss_elimination(uint32_t matrix[][k],uint32_t vektor[])
{
    //Initilaisiere Hilfsvariablen:
    uint32_t imax,wmax;
    uint32_t buffer,buffer2;
    uint32_t f;
    uint32_t A[k][k];
    uint32_t b[k];

    //Belege den Buffer:
    for(int i=0;i<k;i++)
    {
        for(int j=0;j<k;j++)
        {
            A[i][j] = matrix[i][j];
        }
        b[i] = vektor[i];
    }

    //Führe die Gauß-Elimination durch:
    for(int i=0;i<k;i++)
    {
        imax = 0;
        wmax = 0;

        //Finde das Pivotelement:
        for(int j=i;j<k;j++)
        {
            if(A[j][i] > wmax)
            {
                imax = j;
                wmax = A[j][i];
            }
        }
        if(wmax == 0)
        {
            return 0;
        }

        //Vertausche i-te und imax-te Zeile:
        for(int j=0;j<k;j++)
        {
            buffer = A[i][j];
            A[i][j] = A[imax][j];
            A[imax][j] = buffer;
        }
        buffer = b[i];
        b[i] = b[imax];
        b[imax] = buffer;

        for(int j=i+1;j<k;j++)
        {
            buffer = inverse(A[i][i]);
            f = (A[j][i] * buffer) % q;
            for(int l=i+1;l<k;l++)
            {
                A[j][l] = (A[j][l] - (A[i][l]*f) % q + q) % q ;
            }
            b[j] = (b[j] - (b[i]*f)%q + q) % q;

            A[j][i] = 0;
        }
    }

    //Rückwärtssubstitution (Nach TU Chemnitz Numerik Skript Alg 3.1, SoSe 09):
    buffer = inverse(A[k-1][k-1]);
    b[k-1] = (b[k-1] * buffer) % q;

    for(int i=k-1;i>0;i--)
    {
        buffer2 = 0;
        buffer = inverse(A[i-1][i-1]);
        for(int j=i;j<k;j++)
        {
            buffer2 = (buffer2 + (A[i-1][j]*b[j])%q)%q;
        }
        b[i-1] = (((b[i-1] - buffer2 + q)%q)*buffer) % q;
    }

    for(int i=0;i<k;i++)
    {
        vektor[i] = b[i];
    }

    return 1;
}

//Diese Funktion berechnet Gauß (Kombinatorische Algorithmen für LWE, Algorithmus 4)
//Parameter: error[] = Der Fehlervektor, s[] = Das gesuchte Gehemnis, p0 = die Wahrscheinlichkeit, dass e = 0,
//           sbar[] = Variable, in der die Rückgabe gespeichert werden kann
void gauss(uint32_t error[], uint32_t s[], float p0, uint32_t sbar[])
{
    //Parameter für test:
    uint32_t m;
    uint32_t c;
    double x,y;
    float alpha,beta;

    alpha = pow(p0,k)/pow(2,k);
    beta = 1/pow(2,k);
    x = ceil(((sqrt((3*log(1/alpha)*p0)) + sqrt(2*p0*log(1/beta))) / (p0 - (1/q))) * ((sqrt((3*log(1/alpha)*p0)) + sqrt(2*p0*log(1/beta))) / (p0 - (1/q))));
    y = ceil((x/q) + sqrt((3*x*log(1/alpha)*p0)));
    m = (int) x;
    c = (int) y;

    //Initalisiere Hilfvariablen und Parameter des Algorithmus:
    uint32_t A[k][k];
    uint32_t Atest[m][k];
    uint32_t a[k];
    uint32_t b[k];
    uint32_t btest[m];
    uint32_t check2;
    uint32_t check = 0;

    //Initialisiere die Buffer:
    uint32_t sbuf[k];
    uint32_t errorbuf[100];

    for(int i=0;i<k;i++)
    {
        sbuf[i] = s[i];
    }

    for(int i=0;i<100;i++)
    {
        errorbuf[i] = error[i];
    }

    //Generiere die Samples für Test:
    for(int i=0;i<m;i++)
    {
        btest[i] = lweOrakel(errorbuf,sbuf,a);
        for(int j=0;j<k;j++)
        {
            Atest[i][j] = a[j];
        }
    }

    //Führe den eigentlichen Algorithmus aus:
    while(check == 0)
    {
        for(int i=0;i<k;i++)
        {
            b[i] = lweOrakel(errorbuf,sbuf,a);
            for(int j=0;j<k;j++)
            {
                A[i][j] = a[j];
            }
        }
        check2 = gauss_elimination(A,b);

        if(check2 != 0)
        {
            check = test(b,Atest,btest,m,c);
        }
    }

    for(int i=0;i<k;i++)
    {
        sbar[i] = b[i];
    }

    return;
}

//Diese Funktion berechnet Pooled Gauß (Kombinatorische Algorithmen für LWE, Algorithmus 5)
//Parameter: error[] = Der Fehlervektor, s[] = Das gesuchte Gehemnis, p0 = die Wahrscheinlichkeit, dass e = 0,
//           sbar[] = Variable, in der die Rückgabe gespeichert werden kann
void pooled_gauss(uint32_t error[], uint32_t s[], float p0, uint32_t sbar[])
{
    //Parameter für test:
    uint32_t m;
    uint32_t c;
    double x,y;
    float alpha,beta;

    alpha = pow(p0,k)/pow(2,k);
    beta = 1/pow(2,k);
    x = ceil(((sqrt((3*log(1/alpha)*p0)) + sqrt(2*p0*log(1/beta))) / (p0 - (1/q))) * ((sqrt((3*log(1/alpha)*p0)) + sqrt(2*p0*log(1/beta))) / (p0 - (1/q))));
    y = ceil((x/q) + sqrt((3*x*log(1/alpha)*p0)));
    m = (int) x;
    c = (int) y;

    //Lege Hilfsvariablen und Parameter des Algorithmus an:
    uint32_t n = ceil(pow(k,2) * pow(log(k),2));
    uint32_t Atest[m][k];
    uint32_t Apool[n][k];
    uint32_t A[k][k];
    uint32_t a[k];
    uint32_t btest[m];
    uint32_t bpool[n];
    uint32_t b[k];
    uint32_t ck;
    uint32_t index;
    uint32_t check = 0;

    //Initalisiere Buffervariablen:
    uint32_t sbuf[k];
    uint32_t errorbuf[100];

    for(int i=0;i<k;i++)
    {
        sbuf[i] = s[i];
    }

    for(int i=0;i<100;i++)
    {
        errorbuf[i] = error[i];
    }

    //Lege den Pool der Samples an
    for(int i=0;i<n;i++)
    {
        bpool[i] = lweOrakel(errorbuf,sbuf,a);
        for(int j=0;j<k;j++)
        {
            Apool[i][j] = a[j];
        }
    }

    //Generiere die Samples für Test
    for(int i=0;i<m;i++)
    {
        btest[i] = lweOrakel(errorbuf,sbuf,a);
        for(int j=0;j<k;j++)
        {
            Atest[i][j] = a[j];
        }
    }

    //Führe den eigentlichen Algorithmus aus:
    while(check == 0)
    {
        for(int i=0;i<k;i++)
        {
            index = rand() % n;

            for(int j=0;j<k;j++)
            {
                A[i][j] = Apool[index][j];
            }
            b[i] = bpool[index];
        }

        ck = gauss_elimination(A,b);

        if(ck != 0)
        {
            check = test(b,Atest,btest,m,c);
        }
    }

    for(int i=0;i<k;i++)
    {
        sbar[i] = b[i];
    }

    return;
}

//Hier werden die das Gehemnis und der Fehler initialisiert, um anschließend Gauss/Pooled-Gauss aufrufen zu können.
int main()
{
    //Initalisiere Variablen:
    uint32_t s[k];
    uint32_t sbar[k];
    clock_t begin, end;
    float runtime,completetime;

    //Initalisiere die Wahrscheinlichkeit p0:
    float  p0 = 1 / (sqrt(2*PI)*sigma);

    //Initaliziere Zufall:
    time_t  Second;
    Second=time(NULL);
	srand(Second);

    //Initalisiere den Fehlervektor e:
    uint32_t error[100];
    for(int i=0;i<40;i++)
    {
        error[i] = 0;
    }

    for(int i=40;i<100;i++)
    {
        error[i] = (rand()%(q-1))+1;
    }

    //Führe Gauss/Pooled-Gauss in mehreren Durchläufen aus
    completetime = 0;
    uint32_t durchlaufe = 100;
    for(int j=0;j<durchlaufe;j++)
    {
        //Initaliziere das Geheimnis s:
        for(int i=0;i<k;i++)
        {
            s[i] = rand()%q;
        }

        /*
        printf("s = ");
        for(int i=0;i<k;i++)
        {
            printf("%2d ",s[i]);
        }
        printf("\n");
        */

        //Rufe Gauss/Pooled-Gauss auf und messe die Zeit:
        begin = clock();
        pooled_gauss(error,s,p0,sbar);
        end = clock();
        runtime = end - begin;
        runtime = runtime / CLOCKS_PER_SEC;
        completetime = completetime + runtime;

        /*
        printf("s'= ");
        for(int i=0;i<k;i++)
        {
            printf("%2d ",sbar[i]);
        }
        printf("\n");
        */

        //Gebe den Durchlauf aus (zur Fortschrittskontrolle):
        printf("%d",j);
    }

    //Gebe die durchnittliche Laufzeit aus:
    printf("Laufzeit Pooled-Gauss: %.3fs\n",completetime / durchlaufe);

    return 0;
}
