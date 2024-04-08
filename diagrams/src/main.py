import os

import numpy as np
import matplotlib.pyplot as plt


OUT = "target"
EXT = "png"


def standard_normal():
    from scipy.stats import norm
    # Possible values for the distribution
    x = np.linspace(-3, 3, 1000)

    # Creating the figure and the axis
    fig, ax = plt.subplots()

    # Plotting the PDF for the standard normal distribution
    ax.plot(x, norm.pdf(x), label='Standard normal')

    # Adding title and labels
    ax.set_title('Standard normal distribution')
    ax.set_xlabel('Z-score (standard deviations from the mean)')
    ax.set_ylabel('Probability density')

    # Adding a legend
    ax.legend()

    plt.savefig(f"{OUT}/standard_normal.{EXT}")
    plt.close()


def chi_squared():
    def y(x, df):
        from scipy.stats import chi2
        y = chi2.pdf(x, df)
        y[y > 1.0] = np.nan
        return y
    # Degrees of freedom for the distribution
    df_values = [1, 2, 3, 5, 9]
    # Possible values for the distribution
    x = np.linspace(0, 10, 1000)

    # Creating the figure and the axis
    fig, ax = plt.subplots()

    # Plotting the PDF for each value of the degrees of freedom
    for df in df_values:
        ax.plot(x, y(x, df), label=f'df = {df}')

    # Adding title and labels
    ax.set_title('Chi-squared distribution')
    ax.set_xlabel('Chi-squared statistic')
    ax.set_ylabel('Probability density')

    # Adding a legend
    ax.legend()

    plt.savefig(f"{OUT}/chi_squared.{EXT}")
    plt.close()


def bernoulli():
    # Defining the Bernoulli distribution PMF
    def y(p):
        return np.array([1 - p, p])

    # Possible values of p for the distribution
    p_values = [0.1, 0.5, 0.9]
    # Possible outcomes for a Bernoulli distributed variable
    outcomes = np.array([0, 1])

    # Creating the figure and the axis
    fig, ax = plt.subplots()
    # Width of each bar
    width = 0.2

    # Plotting the PMF for each value of p
    for i, p in enumerate(p_values):
        ax.bar(outcomes - width / 2 + i * width - 0.1, y(p), width=width, label=f'p = {p}')

    # Adding title and labels
    ax.set_title('Bernoulli distribution')
    ax.set_xlabel('Outcome')
    ax.set_ylabel('Probability')
    ax.set_xticks(outcomes)  # set the ticks to be the outcome values

    # Adding a legend
    ax.legend()

    plt.savefig(f"{OUT}/bernoulli.{EXT}")
    plt.close()


def binomial():
    # Defining the Binomial distribution PMF
    def y(n, p, k):
        from scipy.stats import binom
        return binom.pmf(k, n, p)

    # Possible values of n for the distribution
    n_values = [5, 10, 20]
    # Possible values of p for the distribution
    p_values = [0.1, 0.5, 0.9]
    # Possible outcomes for a Binomial distributed variable
    outcomes = np.arange(0, 15)

    # Creating the figure and the axis
    fig, ax = plt.subplots()

    # Plotting the PMF for each value of n and p
    for i, n in enumerate(n_values):
        for j, p in enumerate(p_values):
            ax.plot(outcomes, y(n, p, outcomes), 'o-', label=f'n = {n}, p = {p}')

    # Adding title and labels
    ax.set_title('Binomial distribution')
    ax.set_xlabel('Outcome')
    ax.set_ylabel('Probability')
    ax.set_xticks(outcomes)  # set the ticks to be the outcome values

    # Adding a legend
    ax.legend()

    plt.savefig(f"{OUT}/binomial.{EXT}")
    plt.close()


def cauchy():
    # Possible values for the distribution
    x = np.linspace(-10, 10, 1000)

    # Creating the figure and the axis
    fig, ax = plt.subplots()

    # Plotting the PDF for the standard normal distribution
    ax.plot(x, 1 / (np.pi * (1 + x**2)), label='Cauchy')

    # Adding title and labels
    ax.set_title('Cauchy distribution')
    ax.set_xlabel('x')
    ax.set_ylabel('Probability density')

    # Adding a legend
    ax.legend()

    plt.savefig(f"{OUT}/cauchy.{EXT}")
    plt.close()


def dirichlet():
    # Defining the Dirichlet distribution PDF
    def y(alpha, x):
        from scipy.stats import dirichlet
        return dirichlet.pdf(x, alpha)

    # Possible values of alpha for the distribution
    alpha_values = [[1, 1, 1], [2, 2, 2], [0.5, 0.5, 0.5]]
    # Possible values for the distribution
    x_values = [np.random.dirichlet(alpha, size=1000) for alpha in alpha_values]

    # Creating the figure and the axis
    fig, ax = plt.subplots()

    # Plotting the PDF for each value of alpha
    for alpha, x in zip(alpha_values, x_values):
        ax.plot(x, y(alpha, x), label=f'α = {alpha}')

    # Adding title and labels
    ax.set_title('Dirichlet distribution')
    ax.set_xlabel('x')
    ax.set_ylabel('Probability density')

    # Adding a legend
    ax.legend()

    plt.savefig(f"{OUT}/dirichlet.{EXT}")
    plt.close()


def exponential():
    # Defining the Exponential distribution PDF
    def y(lmbda, x):
        from scipy.stats import expon
        return expon.pdf(x, scale=1 / lmbda)

    # Possible values of lambda for the distribution
    lambda_values = [0.5, 1, 2]
    # Possible values for the distribution
    x = np.linspace(0, 5, 1000)

    # Creating the figure and the axis
    fig, ax = plt.subplots()

    # Plotting the PDF for each value of lambda
    for lmbda in lambda_values:
        ax.plot(x, y(lmbda, x), label=f'λ = {lmbda}')

    # Adding title and labels
    ax.set_title('Exponential distribution')
    ax.set_xlabel('x')
    ax.set_ylabel('Probability density')

    # Adding a legend
    ax.legend()

    plt.savefig(f"{OUT}/exponential.{EXT}")
    plt.close()


def gamma():
    # Defining the Gamma distribution PDF
    def y(alpha, beta, x):
        from scipy.stats import gamma
        return gamma.pdf(x, alpha, scale=1 / beta)

    # Possible values of alpha for the distribution
    alpha_values = [1, 2, 3]
    # Possible values of beta for the distribution
    beta_values = [0.5, 1, 2]
    # Possible values for the distribution
    x = np.linspace(0, 10, 1000)

    # Creating the figure and the axis
    fig, ax = plt.subplots()

    # Plotting the PDF for each value of alpha and beta
    for alpha in alpha_values:
        for beta in beta_values:
            ax.plot(x, y(alpha, beta, x), label=f'α = {alpha}, β = {beta}')

    # Adding title and labels
    ax.set_title('Gamma distribution')
    ax.set_xlabel('x')
    ax.set_ylabel('Probability density')

    # Adding a legend
    ax.legend()

    plt.savefig(f"{OUT}/gamma.{EXT}")
    plt.close()


def poisson():
    # Defining the Poisson distribution PMF
    def y(lmbda, k):
        from scipy.stats import poisson
        return poisson.pmf(k, lmbda)

    # Possible values of lambda for the distribution
    lambda_values = [0.5, 1, 2, 4, 10]
    # Possible outcomes for a Poisson distributed variable
    outcomes = np.arange(0, 15)

    # Creating the figure and the axis
    fig, ax = plt.subplots()

    # Plotting the PMF for each value of lambda
    for i, lmbda in enumerate(lambda_values):
        ax.plot(outcomes, y(lmbda, outcomes), 'o-', label=f'λ = {lmbda}')

    # Adding title and labels
    ax.set_title('Poisson distribution')
    ax.set_xlabel('Outcome')
    ax.set_ylabel('Probability')
    ax.set_xticks(outcomes)  # set the ticks to be the outcome values

    # Adding a legend
    ax.legend()

    plt.savefig(f"{OUT}/poisson.{EXT}")
    plt.close()


def weibull():
    # Defining the Frechet distribution PDF
    def y(alpha, x):
        from scipy.stats import weibull_min
        return weibull_min.pdf(x, alpha)

    # Possible values of alpha for the distribution
    alpha_values = [0.5, 1, 2]
    # Possible values for the distribution
    x = np.linspace(0, 5, 1000)

    # Creating the figure and the axis
    fig, ax = plt.subplots()

    # Plotting the PDF for each value of alpha
    for alpha in alpha_values:
        ax.plot(x, y(alpha, x), label=f'α = {alpha}')

    # Adding title and labels
    ax.set_title('Frechet distribution')
    ax.set_xlabel('x')
    ax.set_ylabel('Probability density')

    # Adding a legend
    ax.legend()

    plt.savefig(f"{OUT}/frechet.{EXT}")
    plt.close()


if __name__ == "__main__":
    # Recursively delete the output directory
    for root, dirs, files in os.walk(OUT, topdown=False):
        for file in files:
            os.remove(os.path.join(root, file))
        for dir in dirs:
            os.rmdir(os.path.join(root, dir))
    standard_normal()
    bernoulli()
    chi_squared()
    binomial()
    cauchy()
    dirichlet()
    exponential()
    gamma()
    poisson()
    weibull()
